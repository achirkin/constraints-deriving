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
import           Data.List           (groupBy, isPrefixOf, nubBy, sortOn)
import           Data.Maybe          (catMaybes, fromMaybe)
import           Data.Monoid
import qualified FamInstEnv
import           InstEnv             (ClsInst, DFunInstType)
import qualified InstEnv
import qualified OccName
import           Panic               (panicDoc)
import           TcType              (tcSplitDFunTy)
import qualified Unify

import Data.Constraint.Deriving.CorePluginM

-- | A marker to tell the core plugin to derive all visible class instances
--      for a given newtype.
--
--   The deriving logic is to simply re-use existing instance dictionaries
--      by type-casting.
data DeriveAll
  = DeriveAll
    -- ^ Same as @DeriveAllBut []@.
  | DeriveAllBut { _ignoreList :: [String] }
    -- ^ Specify a list of class names to ignore
  | DeriveAll' { _forcedMode :: OverlapMode, _ignoreList :: [String] }
    -- ^ Specify an overlap mode and a list of class names to ignore
  deriving (Eq, Show, Read, Data)


-- | This type family is used to impose constraints on type parameters when
--   looking up type instances for the `DeriveAll` core plugin.
--
--   `DeriveAll` uses only those instances that satisfy the specified constraint.
--   If the constraint is not specified, it is assumed to be `()`.
type family DeriveContext (t :: Data.Kind.Type) :: Data.Kind.Constraint

-- | Run `DeriveAll` plugin pass
deriveAllPass :: CorePluginEnvRef -> CoreToDo
deriveAllPass eref = CoreDoPluginPass "Data.Constraint.Deriving.DeriveAll"
  -- if a plugin pass totally fails to do anything useful,
  -- copy original ModGuts as its output, so that next passes can do their jobs.
  (\x -> fromMaybe x <$> runCorePluginM (deriveAllPass' x) eref)

{-
  Derive all specific instances of a type for its newtype wrapper.

  Steps:

  1. Lookup a type or type family instances (branches of CoAxiom)
       of referenced by the newtype decl

  2. For every type instance:

     2.1 Lookup all class instances

     2.2 For every class instance:

         * Use mkLocalInstance with parameters of found instance
             and replaced RHS types
         * Create a corresponding top-level binding (DFunId),
             add it to mg_binds of ModGuts.
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
      | Just ((xn, da):ds) <- lookupUFM anns x = do
      unless (null ds) $
        pluginLocatedWarning (nameSrcSpan xn) $
          "Ignoring redundant DeriveAll annotations" $$
          hcat
          [ "(the plugin needs only one annotation per type declaration, but got "
          , speakN (length ds + 1)
          , ")"
          ]
      pluginDebug $ "DeriveAll invoked on TyCon" <+> ppr x
      (newInstances, newBinds) <- unzip . fromMaybe [] <$> try (deriveAll da x guts)
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
  The first thing I do here is to make sure this
    is indeed a proper newtype declaration.
  Then, lookup the DeriveContext-specified constraints.
  Then, enumerate specific type instances (based on constraints
    and type families in the newtype def.)
  Then, lookup all class instances for the found type instances.
 -}
deriveAll :: DeriveAll -> TyCon -> ModGuts -> CorePluginM [(InstEnv.ClsInst, CoreBind)]
deriveAll da tyCon guts
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
      r <- join <$> traverse (lookupMatchingInstances da guts) allMatchingTypes
      pluginDebug
        . hang "DeriveAll (3): matching class instances:" 2
        . vcat $ map (ppr . fst) r
      return $ filterDupInsts r

-- not a good newtype declaration
  | otherwise
    = pluginLocatedError
       (nameSrcSpan $ tyConName tyCon)
       "DeriveAll works only on plain newtype declarations"

  where
    -- O(n^2) search for duplicates. Slow, but what else can I do?..
    filterDupInsts = nubBy $ \(x,_) (y, _) -> InstEnv.identicalClsInstHead x y
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
                  [ "I faced an impossible type when"
                      <+> "matching an instance of type family DeriveContext:"
                  , ppr i, "at"
                  , ppr $ nameSrcSpan $ getName i]
            rhs = FamInstEnv.fi_rhs i
        in (tys, rhs)


-- | Find all instance of a type family in scope by its TyCon.
lookupTyFamInstances :: ModGuts -> TyCon -> CorePluginM [FamInstEnv.FamInst]
lookupTyFamInstances guts fTyCon = do
    pkgFamInstEnv <- liftCoreM getPackageFamInstEnv
    return $ FamInstEnv.lookupFamInstEnvByTyCon
               (pkgFamInstEnv, mg_fam_inst_env guts) fTyCon

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
    -- ^ Irreducible constraints
    --      (I can prepend them in the class instance declarations)
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
    , "{ mtCtxEqs      =" <+> ppr mtCtxEqs
    , ", mtTheta       =" <+> ppr mtTheta
    , ", mtOverlapMode =" <+> text (show mtOverlapMode)
    , ", mtBaseType    =" <+> ppr mtBaseType
    , ", mtNewType     =" <+> ppr mtNewType
    , ", mtIgnorelist  =" <+> ppr mtIgnoreList
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

-- | try to get rid of mtCtxEqs by replacing tyvars
--       by rhs in all components of the MatchingType
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
        in go (map (second (map $ substTyAddInScope sub)) xs)
              $ substMatchingType sub mt
    -- TyVar occurs more than once: it may indicate
    --       a trivial substition or contradiction
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


-- | Try to strip trailing TyVars from the base and newtypes,
--   thus matching higher-kinded types.
--   This way I can also derive things like Monad & co
tryHigherRanks :: MatchingType -> [MatchingType]
tryHigherRanks mt@MatchingType {..}
  | Just (mtBaseType', bt) <- splitAppTy_maybe mtBaseType
  , Just (mtNewType' , nt) <- splitAppTy_maybe mtNewType
  , Just btv <- getTyVar_maybe bt
  , Just ntv <- getTyVar_maybe nt
  , btv == ntv
    -- No constraints or anything else involving our TyVar
  , notElem btv
        . (map fst mtCtxEqs ++)
        . tyCoVarsOfTypesWellScoped
      $ [mtBaseType', mtNewType']
        ++ map snd mtCtxEqs
        ++ mtTheta
        ++ mtIgnoreList
  = let mt' = mt
          { mtBaseType = mtBaseType'
          , mtNewType  = mtNewType'
          }
    in mt : tryHigherRanks mt'
tryHigherRanks mt = [mt]

-- | For a given type and constraints, enumerate all possible concrete types;
--   specify overlapping mode if encountered with conflicting instances of
--   closed type families.
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
    (>>= tryHigherRanks . cleanupMatchingType)
         . take 1000 -- TODO: improve the logic and the termination rule
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
  [1] Add new tyVar ~ TypeFamily, from type family occurrences
       in the base or newtypes
      (but also check this type family is not present in the eqs?)
  [2] Remove an item (TypeFamily) from the list by substituting
        all possible type family instances
      into the the base type, the newtype, and the list of constraints.
  [3] Remove a non-TypeFamily item (i.e. a proper data/newtype TyCon)
      by substituting TyVar with
      this type in the base type, the newtype, and the list of constraints.

  Actions [1,2] may lead to an infinite expansion (recursive families)
  so I need to bound the number of iterations. An approximate implementation plan:
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
        in if eqType ft rezt
           then mt { mtIgnoreList = ft : mtIgnoreList }
           else replaceTyMatchingType famOcc rezt newMt
                  { mtOverlapMode = omode }


    -- Lookup through all components
    look = First . lookupFamily mtIgnoreList
    First mfam = mconcat
      [ foldMap (look . snd) mtCtxEqs
      , foldMap look mtTheta
      , look mtBaseType
      , look mtNewType
      ]


-- -- TODO: Not sure if I need it at all;
--                   most of the API functions look through synonyms
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
--   such that original type family can be replaced with any
--     of the types in the output list.
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
    = withFamily ft (pure Nothing) $ const $ expandClosedFamily os bcs
  where
    bcs = fromBranches $ coAxiomBranches coax
    os  = if all (null . coAxBranchIncomps) bcs
          then repeat NoOverlap else map overlap bcs
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
                   -> [Type] -> CorePluginM (Maybe [(OverlapMode, Type, TCvSubst)])
-- empty type family -- leave it as-is
expandClosedFamily _ [] _ = pure Nothing
expandClosedFamily os bs fTyArgs = fmap (Just . catMaybes) $ traverse go $ zip os bs
  where
    go (om, cb) = do
      let flhs' = coAxBranchLHS cb
          n = length flhs'
          tvs' = tyCoVarsOfTypesWellScoped flhs'
      tvs <- traverse freshenTyVar tvs'
      let freshenSub = zipTvSubst tvs' $ map mkTyVarTy tvs
          flhs = substTys freshenSub flhs'
          frhs = substTyAddInScope freshenSub $ coAxBranchRHS cb
          t = foldl mkAppTy frhs $ drop n fTyArgs
          msub = Unify.tcMatchTys (take n fTyArgs) flhs
      return $ (,,) om t <$> msub



-- | The same as `expandFamily`, but I know already that the family is open.
expandOpenFamily :: ModGuts
                 -> TyCon  -- ^ Type family construtor
                 -> [Type] -- ^ Type family arguments
                 -> CorePluginM (Maybe [(OverlapMode, Type, TCvSubst)])
expandOpenFamily guts fTyCon fTyArgs = do
  tfInsts <- lookupTyFamInstances guts fTyCon
  if null tfInsts
    then pure $ Just [] -- No mercy
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
  if null tfInsts
    then pure $ Just [] -- No mercy
    else sequence <$> traverse expandDInstance tfInsts
  where
    expandDInstance inst
      | fitvs <- FamInstEnv.fi_tvs inst
      = do
      tvs <- traverse freshenTyVar fitvs
      let freshenSub = zipTvSubst fitvs $ map mkTyVarTy tvs
          fitys = substTys freshenSub $ FamInstEnv.fi_tys inst
          instTyArgs = align fTyArgs fitys
      return $ (,,) NoOverlap (mkTyConApp fTyCon instTyArgs)
        <$> Unify.tcMatchTys fTyArgs instTyArgs
    align [] _          = []
    align xs []         = xs
    align (_:xs) (y:ys) = y : align xs ys


data MatchingInstance = MatchingInstance
  { miInst       :: ClsInst
    -- ^ Original found instance for the base type (as declared somewhere);
    --   It contains the signature and original DFunId
  , miInstTyVars :: [DFunInstType]
    -- ^ How TyVars of miOrigBaseClsInst should be replaced to make it as
    --   an instance for the base type;
    --   e.g. a TyVar may be instantiated with a concrete type
    --         (which may or may not contain more type variables).
  , miTheta      :: [(PredType, MatchingPredType)]
    -- ^ Original pred types and how they are going to be transformed
  }

instance Outputable MatchingInstance where
  ppr MatchingInstance {..} = hang "MatchingInstance" 2 $ vcat
    [ "{ miInst       =" <+> ppr miInst
    , ", miInstTyVars =" <+> ppr miInstTyVars
    , ", miTheta      =" <+> ppr miTheta
    ]

{-
Resolving theta types:

1. Class constraints: every time check
   a. if there is an instance, substitute corresponding DFunIds and be happy.
   b. if there is no instance and no tyvars, then fail
   c. otherwise propagate the constraint further.

2. Equality constraints: check equality
   a. Types are equal (and tyvars inside equal as well):
      Substitute mkReflCo
   b. Types are unifiable:
      Propagate constraint further
   c. Types are non-unifiable:
      Discard the whole instance declaration.
 -}
data MatchingPredType
  = MptInstance MatchingInstance
    -- ^ Found an instance
  | MptReflexive Coercion
    -- ^ The equality become reflexive after a tyvar substitution
  | MptPropagateAs PredType
    -- ^ Could do nothing, but there is still hope due to the present tyvars

instance Outputable MatchingPredType where
  ppr (MptInstance x)    = "MptInstance" <+> ppr x
  ppr (MptReflexive x)   = "MptReflexive" <+> ppr x
  ppr (MptPropagateAs x) = "MptPropagateAs" <+> ppr x

findInstance :: InstEnv.InstEnvs
             -> Type
             -> ClsInst
             -> Maybe MatchingInstance
findInstance ie t i
  | -- Most important: some part of the instance parameters must unify to arg
    Just sub <- getFirst $ foldMap (First . flip (recMatchTyKi False) t) iTyPams
    -- substituted type parameters of the class
  , newTyPams <- map (substTyAddInScope sub) iTyPams
    -- This tells us how instance tyvars change after matching the type
    = matchInstance ie iClass newTyPams
  | otherwise
    = Nothing
  where
    (_, _, iClass, iTyPams) = InstEnv.instanceSig i


matchInstance :: InstEnv.InstEnvs
              -> Class
              -> [Type]
              -> Maybe MatchingInstance
matchInstance ie cls ts
  | ([(i, tyVarSubs)], _notMatchButUnify, _safeHaskellStuff)
      <- InstEnv.lookupInstEnv False ie cls ts
  , (iTyVars, iTheta, _, _) <- InstEnv.instanceSig i
  , sub <- mkTvSubstPrs
         . catMaybes $ zipWith (fmap . (,)) iTyVars tyVarSubs
    = do
    -- the following line checks if constraints are solvable and fails otherwise
    mpts <- traverse (matchPredType ie . substTyAddInScope sub) iTheta
    return MatchingInstance
      { miInst = i
      , miInstTyVars = tyVarSubs
      , miTheta = zip iTheta mpts
      }
  | otherwise
    = Nothing

matchPredType :: InstEnv.InstEnvs
              -> PredType
              -> Maybe MatchingPredType
matchPredType ie pt = go $ classifyPredType pt
  where
    go (ClassPred cls ts)
      | Just mi <- matchInstance ie cls ts
                       = Just $ MptInstance mi
        -- we could not find an instance, but also there are no tyvars (and no hope)
      | [] <- tyCoVarsOfTypesWellScoped ts
                       = Nothing
      | otherwise      = Just $ MptPropagateAs pt
    go (EqPred rel t1 t2)
      | eqType t1 t2   = Just . MptReflexive $ case rel of
                                          NomEq  -> mkReflCo Nominal t1
                                          ReprEq -> mkReflCo Representational t1
      | Unify.typesCantMatch [(t1,t2)]
                       = Nothing
      | otherwise      = Just $ MptPropagateAs pt
    go _               = Just $ MptPropagateAs pt


type TyExp = (Type, CoreExpr)
type TyBndr = (Type, CoreBndr)


mtmiToExpression :: MatchingType
                 -> MatchingInstance
                 -> CorePluginM TyExp
mtmiToExpression MatchingType {..} mi = do
  (bndrs, (tOrig, e)) <- miToExpression' [] mi
  let extraTheta
            = filter (\t -> not $ any (eqType t . fst) bndrs) mtTheta
      tRepl = replaceTypeOccurrences mtBaseType mtNewType tOrig
      tFun  = mkInvisFunTys (extraTheta ++ map fst bndrs) tRepl
      tvs   =  tyCoVarsOfTypeWellScoped tFun
  return
    ( mkSpecForAllTys tvs tFun
    , mkCoreLams (tvs ++ map mkWildValBinder extraTheta ++ map snd bndrs)
      $ mkCast e
      $ mkUnsafeCo Representational tOrig tRepl
    )


-- | Construct a core expression and a corresponding type.
--   It does not bind arguments;
--   uses only types and vars present in MatchingInstance;
--   may create a few vars for PredTypes, they are returned in fst.
miToExpression' :: [TyExp]
                   -- ^ types and expressions of the PredTypes that are in scope
                -> MatchingInstance
                -> CorePluginM ([TyBndr], TyExp)
                   -- (what to add to lambda, and the final expression)
miToExpression' availPTs MatchingInstance {..} = do
    (bndrs, eArgs) <- addArgs availPTs $ map snd miTheta
    return
      ( bndrs
      , ( newIHead
        , mkCoreApps eDFunWithTyPams eArgs
        )
      )
  where
    (iTyVars, _, iClass, iTyPams) = InstEnv.instanceSig miInst
    -- this is the same length as iTyVars, needs to be applied on dFunId
    tyVarVals = zipWith (fromMaybe . mkTyVarTy) iTyVars miInstTyVars
    sub = mkTvSubstPrs . catMaybes
          $ zipWith (fmap . (,)) iTyVars miInstTyVars
    newTyPams = map (substTyAddInScope sub) iTyPams
    newIHead = mkTyConApp (classTyCon iClass) newTyPams
    eDFun = Var $ InstEnv.instanceDFunId miInst
    eDFunWithTyPams = mkTyApps eDFun tyVarVals
    addArgs :: [TyExp]
            -> [MatchingPredType]
            -> CorePluginM ([TyBndr], [CoreExpr])
    addArgs _   []    = pure ([], [])
    addArgs ps (x:xs) = do
      (tbdrs, e) <- mptToExpression ps x
      let ps' = ps ++ map (Var <$>) tbdrs
      (tbdrs', es) <- addArgs ps' xs
      return
        ( tbdrs ++ tbdrs'
        , e:es
        )


-- | Construct an expression to put as a PredType argument.
--   It may need to produce a new type variable.
mptToExpression :: [TyExp]
                -> MatchingPredType
                -> CorePluginM ([TyBndr], CoreExpr)
mptToExpression ps (MptInstance mi)
  = fmap snd <$> miToExpression' ps mi
mptToExpression _  (MptReflexive c)
  = pure ([], Coercion c)
mptToExpression ps (MptPropagateAs pt)
  = case mte of
    Just e -> pure ([], e)
    Nothing -> do
      loc <- liftCoreM getSrcSpanM
      u <- getUniqueM
      let n = mkInternalName u
                (mkOccName OccName.varName $ "dFunArg_" ++ show u) loc
          v = mkLocalIdOrCoVar n pt
      return ([(pt,v)], Var v)
  where
      mte = getFirst $ foldMap getSamePT ps
      getSamePT (t, e)
        | eqType t pt = First $ Just e
        | otherwise    = First Nothing

-- | For a given most concrete type, find all possible class instances.
--   Derive them all by creating a new CoreBind with a casted type.
--
--   Prerequisite: in the tripple (overlapmode, baseType, newType),
--   TyVars of the newType must be a superset of TyVars of the baseType.
lookupMatchingInstances :: DeriveAll
                        -> ModGuts
                        -> MatchingType
                        -> CorePluginM [(ClsInst, CoreBind)]
lookupMatchingInstances da guts mt
    | Just bTyCon <- tyConAppTyCon_maybe $ mtBaseType mt = do
      ie <- getInstEnvs guts
      let clsInsts = lookupClsInsts ie bTyCon
      pluginDebug $ hang "lookupMatchingInstances candidate instances:" 2 $
        vcat $ map ppr clsInsts
      catMaybes <$> traverse (lookupMatchingInstance da ie mt) clsInsts
    | otherwise = fmap (const []) . pluginDebug $ hcat
        [ text "DeriveAll.lookupMatchingInstances found no class instances for "
        , ppr (mtBaseType mt)
        , text ", because it could not get the type constructor."
        ]


lookupMatchingInstance :: DeriveAll
                       -> InstEnv.InstEnvs
                       -> MatchingType
                       -> ClsInst
                       -> CorePluginM (Maybe (ClsInst, CoreBind))
lookupMatchingInstance da ie mt@MatchingType {..} baseInst
  | not . unwantedName da $ getName iClass
  , all (noneTy (unwantedName DeriveAll)) iTyPams
    = case findInstance ie mtBaseType baseInst of
        Just mi -> do
          (t, e) <- mtmiToExpression mt mi
          newN <- newName (occNameSpace baseDFunName)
            $ occNameString baseDFunName
              ++ show (getUnique baseDFunId) -- unique per baseDFunId
              ++ newtypeNameS                -- unique per newType
          let (newTyVars, _, _, newTyPams) = tcSplitDFunTy t
              newDFunId = mkExportedLocalId
                (DFunId isNewType) newN t
          return $ Just
            ( InstEnv.mkLocalInstance
                          newDFunId
                          ( deriveAllMode da $ mappend mtOverlapMode baseOM )
                          newTyVars iClass newTyPams
            , NonRec newDFunId e
            )
        Nothing
            -- in case if the instance is more specific than the MatchingType,
            -- substitute types and try again
          | Just sub <- getFirst
              $ foldMap (First . flip (recMatchTyKi True) mtBaseType) iTyPams
          , not $ isEmptyTCvSubst sub
            -> do
            pluginDebug $ hang "Could not find an instance, trying again:" 2 $ vcat
              [ text "Base type:" <+> ppr mtBaseType
              , text "Instance:" <+> ppr baseInst
              , text "Substitution:" <+> ppr sub
              ]
            lookupMatchingInstance da ie (substMatchingType sub mt) baseInst
          | otherwise
            -> do
            pluginDebug $ hang "Ignored instance" 2 $ vcat
              [ text "Base type:" <+> ppr mtBaseType
              , text "Instance:" <+> ppr baseInst
              ]
            pure Nothing
  | otherwise
    = pure Nothing
  where
    deriveAllMode (DeriveAll' m _) _ = toOverlapFlag m
    deriveAllMode  _               m = toOverlapFlag m
    baseOM = instanceOverlapMode baseInst
    baseDFunId = InstEnv.instanceDFunId baseInst
    (_, _, iClass, iTyPams) = InstEnv.instanceSig baseInst
    isNewType = isNewTyCon (classTyCon iClass)
    baseDFunName = occName . idName $ baseDFunId
    newtypeNameS = case tyConAppTyCon_maybe mtNewType of
      Nothing -> "DeriveAll-generated"
      Just tc -> occNameString $ occName $ tyConName tc


-- checks if none of the names in the type satisfy the predicate
noneTy :: (Name -> Bool) -> Type -> Bool
noneTy f = not . uniqSetAny f . orphNamesOfType

unwantedName :: DeriveAll -> Name -> Bool
unwantedName da n
  | modName == "GHC.Generics"  = True
  | modName == "Data.Typeable" = True
  | modName == "Data.Data"     = True
  | "Language.Haskell.TH"
          `isPrefixOf` modName = True
  | valName == "Coercible"     = True
  | DeriveAllBut xs <- da
  , valName `elem` xs          = True
  | DeriveAll' _ xs <- da
  , valName `elem` xs          = True
  | otherwise                  = False
  where
    modName = moduleNameString . moduleName $ nameModule n
    valName = occNameString $ getOccName n
