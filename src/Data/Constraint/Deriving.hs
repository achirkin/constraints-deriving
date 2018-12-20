{-# LANGUAGE CPP                #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RecordWildCards    #-}
{-# OPTIONS_GHC -fno-warn-orphans       #-}
module Data.Constraint.Deriving (plugin, ToInstance (..)) where

import           Class
import           CoAxiom
import           Data.Data   (Data)
import           Data.Maybe  (catMaybes, fromMaybe, mapMaybe, maybeToList)
import           Data.Monoid (Any (..), First (..))
import qualified Finder
import           GhcPlugins
import qualified IfaceEnv
import           InstEnv
import           Panic       (panicDoc)
import qualified TcRnMonad

-- | A marker to tell the core plugin to convert BareConstraint top-level binding into
--   an instance declaration.
data ToInstance
  = ToInstance
  | ToInstanceOverlappable
  | ToInstanceOverlapping
  | ToInstanceOverlaps
  | ToInstanceIncoherent
  deriving (Eq, Show, Data)

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
  bf <- lookupBackendFamily
  bc <- lookupBareConstraintT
  return ( CoreDoPluginPass "Data.Constraint.Deriving" (deriveAllInstances bf)
         : CoreDoPluginPass "Data.Constraint.Deriving" (toInstance bc)
         : todo)

{-
  Derive all specific instances of `Backend t n` for `DFBackend t n b`

  I want to make all specific instances for DFBackend and different backend types

  Since I guarantee that DFBackend is a newtype wrapper with exactly the same
  behavior as the backends, I don't even want to derive the instance using
  the usual machinery. Just declare all instances with existing DFunIds.

  Steps:

  1. Lookup type family instances (branches of CoAxiom) of Backend t n

  2. For every type instance:

     2.1 Lookup all class instances

     2.2 For every class instance:

         * Use mkLocalInstance with parameters of found instance
           and replaced RHS types
         * Add new instance to (mg_insts :: ![ClsInst]) of ModGuts

 -}
deriveAllInstances :: CoAxiom Branched -> ModGuts -> CoreM ModGuts
deriveAllInstances backendFamily guts = do

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
                        then Overlapping NoSourceText
                        else Incoherent NoSourceText

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
                  -> Maybe ClsInst
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
                    (OverlapFlag overlapMode False)
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
    mkBind :: DFunId -> ClsInst -> CoreBind
    mkBind oldId newInst
        = NonRec newId
        $ Cast (Var oldId)
        $ mkUnsafeCo Representational (idType oldId) (idType newId)
      where
        newId = instanceDFunId newInst


toInstance :: TyCon -> ModGuts -> CoreM ModGuts
toInstance bareConstraintTc guts = do

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
    toInst :: CoreBind -> ([ClsInst], CoreBind)
    toInst cb@(NonRec cbVar  cbE)
      | [omode] <- getOFlag <$> getToInstanceAnns cb
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

    getOFlag i = OverlapFlag (getOMode i) False
    getOMode ToInstance             = NoOverlap NoSourceText
    getOMode ToInstanceOverlapping  = Overlapping NoSourceText
    getOMode ToInstanceOverlappable = Overlappable NoSourceText
    getOMode ToInstanceOverlaps     = Overlaps NoSourceText
    getOMode ToInstanceIncoherent   = Incoherent NoSourceText

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




lookupBackendFamily :: CoreM (CoAxiom Branched)
lookupBackendFamily = do
    hscEnv <- getHscEnv
    md <- liftIO $ lookupModule hscEnv mdName pkgNameFS
    backendName <- liftIO
        $ TcRnMonad.initTcRnIf '?' hscEnv () ()
        $ IfaceEnv.lookupOrig md (mkTcOcc "Backend")
    (eps, hpt) <- liftIO $
        TcRnMonad.initTcRnIf '?' hscEnv () () TcRnMonad.getEpsAndHpt
    backendTyCon <- lookupTyCon backendName

    let getArrayAxiom ca@CoAxiom {..}
          | co_ax_tc == backendTyCon = Just ca
          | otherwise                = Nothing
        cas =  mapMaybe getArrayAxiom $ (do
          hmi <- maybeToList $ lookupHpt hpt (moduleName md)
          typeEnvCoAxioms . md_types $ hm_details hmi
          ) ++ typeEnvCoAxioms (eps_PTE eps)

    return $ case cas of
      []   -> panicDoc "Data.Constraint.Deriving" $
        "Could not find instances of the closed type family" <> ppr backendTyCon
      ca:_ -> ca
  where
    mdName = mkModuleName "Lib.BackendFamily"
    pkgNameFS = fsLit "this"


lookupBareConstraintT :: CoreM TyCon
lookupBareConstraintT = do
    hscEnv <- getHscEnv
    md <- liftIO $ lookupModule hscEnv mdName pkgNameFS
    backendName <- liftIO
        $ TcRnMonad.initTcRnIf '?' hscEnv () ()
        $ IfaceEnv.lookupOrig md (mkTcOcc "BareConstraint")
    lookupTyCon backendName
  where
    mdName = mkModuleName "Data.Constraint.Bare"
    pkgNameFS = fsLit "constraints-deriving"




lookupModule :: HscEnv
             -> ModuleName
             -> FastString
             -> IO Module
lookupModule hscEnv mdName pkg = go [Just pkg, Just (fsLit "this")]
  where
    go [] = panicDoc "Data.Constraint.Deriving" $
      "Could not find module " <> ppr mdName
    go (x:xs) = findIt x >>= \case
      Nothing -> go xs
      Just md -> return md

    findIt = fmap getIt . Finder.findImportedModule hscEnv mdName
    getIt (Found _ md)                = Just md
    getIt (FoundMultiple ((md, _):_)) = Just md
    getIt _                           = Nothing




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

