{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
module Data.Constraint.Deriving.ToInstance
  ( ToInstance (..)
  , OverlapMode (..)
  , toInstancePass
  , CorePluginEnvRef, initCorePluginEnv
  ) where

import Control.Applicative (Alternative (..))
import Control.Monad       (join, unless)
import Data.Data           (Data)
import Data.Maybe          (fromMaybe, isJust)
import Data.Monoid         (First (..))

import Data.Constraint.Deriving.CorePluginM
import Data.Constraint.Deriving.Import
import Data.Constraint.Deriving.OverlapMode


{- | A marker to tell the core plugin to convert a top-level `Data.Constraint.Dict` binding into
     an instance declaration.

     Example:

@
type family FooFam a where
  FooFam Int = Int
  FooFam a   = Double

data FooSing a where
  FooInt   :: FooSing Int
  FooNoInt :: FooSing a

class FooClass a where
  fooSing :: FooSing a

newtype Bar a = Bar (FooFam a)

{\-\# ANN fooNum (ToInstance NoOverlap) \#-\}
fooNum :: forall a . Dict (Num (Bar a))
fooNum = mapDict (unsafeDerive Bar) $ case fooSing @a of
  FooInt   -> Dict
  FooNoInt -> Dict
@

     Note:

     * `fooNum` should be exported by the module
        (otherwise, it may be optimized-out before the core plugin pass);
     * Constraints of the function become constraints of the new instance;
     * The argument of `Dict` must be a single class (no constraint tuples or equality constraints);
     * The instance is created in a core-to-core pass, so it does not exist for the type checker in the current module.
 -}
newtype ToInstance = ToInstance { overlapMode :: OverlapMode }
  deriving (Eq, Show, Read, Data)

-- | Run `ToInstance` plugin pass
toInstancePass :: CorePluginEnvRef -> CoreToDo
toInstancePass eref = CoreDoPluginPass "Data.Constraint.Deriving.ToInstance"
  -- if a plugin pass totally  fails to do anything useful,
  -- copy original ModGuts as its output, so that next passes can do their jobs.
  (\x -> fromMaybe x <$> runCorePluginM (toInstancePass' x) eref)

toInstancePass' :: ModGuts -> CorePluginM ModGuts
toInstancePass' gs = go (reverse $ mg_binds gs) annotateds gs
  where
    annotateds :: UniqMap [(Name, ToInstance)]
    annotateds = getModuleAnns gs

    go :: [CoreBind] -> UniqMap [(Name, ToInstance)] -> ModGuts -> CorePluginM ModGuts
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
      | Just ((xn, ti):ds) <- lookupUFM anns (getUnique x) = do
      unless (null ds) $
        pluginLocatedWarning (nameSrcSpan xn) $
          "Ignoring redundant ToInstance annotations" $$
          hcat
          [ "(the plugin needs only one annotation per binding, but got "
          , speakN (length ds + 1)
          , ")"
          ]
      -- add new definitions and continue
      try (toInstance ti cbx) >>= \case
        Nothing
          -> go xs (delFromUFM anns (getUnique x)) guts
        Just (newInstance, newBind)
          -> go xs (delFromUFM anns (getUnique x))
              (replaceInstance newInstance newBind guts)
                { -- Remove original binding from the export list
                  --                                if it was there.
                  mg_exports  = filterAvails (xn /=) $ mg_exports guts
                }

    -- ignore the rest of bindings
    go (_:xs) anns guts = go xs anns guts

    pprBulletNameLoc n = hsep
      [" " , bullet, ppr $ occName n, ppr $ nameSrcSpan n]
    pprNotes = vcat . map (\x -> hsep [" ", bullet, x])

-- | Transform a given CoreBind into an instance.
--
--   The input core bind must have type `Ctx => Dict (Class t1 .. tn)`
--
--   The output is `instance {-# overlapMode #-} Ctx => Class t1 ... tn`
toInstance :: ToInstance -> CoreBind -> CorePluginM (ClsInst, CoreBind)

toInstance _ (Rec xs) = do
    loc <- liftCoreM getSrcSpanM
    pluginLocatedError
        (fromMaybe loc $ getFirst $ foldMap (First . Just . nameSrcSpan . getName . fst) xs)
      $ "ToInstance plugin pass does not support recursive bindings"
      $$ hsep ["(group:", pprQuotedList (map (getName . fst) xs), ")"]

toInstance (ToInstance omode) (NonRec bindVar bindExpr) = do
    -- check if all type arguments are constraint arguments
    unless (all (tcIsConstraintKind . typeKind) theta) $
      pluginLocatedError loc notGoodMsg

    -- get necessary definitions
    tcBareConstraint <- ask tyConBareConstraint
    tcDict <- ask tyConDict
    fDictToBare <- ask funDictToBare
    varCls <- newTyVar constraintKind
    let tyMatcher = mkTyConApp tcDict [mkTyVarTy varCls]

    -- Get instance definition
    match <- case tcMatchTy tyMatcher dictTy of
      Nothing -> pluginLocatedError loc notGoodMsg
      Just ma -> pure ma
    let matchedTy = substTyVar match varCls
        instSig = mkSpecForAllTys bndrs $ mkInvisFunTysMany theta matchedTy
        bindBareTy = mkSpecForAllTys bndrs $ mkInvisFunTysMany theta $ mkTyConApp tcBareConstraint [matchedTy]

    -- check if constraint is indeed a class and get it
    matchedClass <- case tyConAppTyCon_maybe matchedTy >>= tyConClass_maybe of
      Nothing -> pluginLocatedError loc notGoodMsg
      Just cl -> pure cl

    -- try to apply dictToBare to the expression of the found binding
    mnewExpr <- try $ unwrapDictExpr dictTy fDictToBare bindExpr
    newExpr  <- case mnewExpr of
      Nothing -> pluginLocatedError loc notGoodMsg
      Just ex -> pure $ mkCast ex
                      $ mkPluginCo "(BareConstraint c ~ c)" Representational bindBareTy instSig


    mkNewInstance omode matchedClass bindVar newExpr

  where
    origBindTy = idType bindVar
    (bndrs, bindTy) = splitForAllTys origBindTy
    (theta, dictTy) = splitFunTysCompat bindTy
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
              -> CorePluginM (ClsInst, CoreBind)
mkNewInstance omode cls bindVar bindExpr = do
    n <- newName varName
       $ getOccString bindVar ++ "_ToInstance"
    let iDFunId = mkExportedLocalId
          (DFunId $ isNewTyCon (classTyCon cls))
          n itype
    return
      ( mkLocalInstance iDFunId ioflag tvs cls tys
      , NonRec iDFunId bindExpr
      )
  where
    ioflag  = toOverlapFlag omode
    itype   = exprType bindExpr

    (tvs, itype') = splitForAllTys itype
    (_, typeBody) = splitFunTysCompat itype'
    tys = fromMaybe aAaaOmg $ tyConAppArgs_maybe typeBody
    aAaaOmg = panicDoc "ToInstance" $ hsep
      [ "Impossible happened:"
      , "expected a class constructor in mkNewInstance, but got"
      , ppr typeBody
      , "at", ppr $ nameSrcSpan $ getName bindVar
      ]


-- | Go through type applications and apply dictToBare function on `Dict c` type
unwrapDictExpr :: Type
                  -- ^ Dict c
                  --
                  --   Serves as stop test (if rhs expression matches the type)
               -> Id
                  -- ^ dictToBare :: forall (c :: Constraint) . Dict c -> BareConstraint c
               -> CoreExpr
                  -- ^ forall a1..an . (Ctx1,.. Ctxn) => Dict c
               -> CorePluginM CoreExpr
                  -- ^ forall a1..an . (Ctx1,.. Ctxn) => BareConstraint c
unwrapDictExpr dictT unwrapFun ex = case ex of
    Var _      -> testNWrap unwrapFail <|> (mkLamApp >>= proceed)
    Lit _      -> testNWrap unwrapFail
    App e a    -> testNWrap $ (App e <$> proceed a) <|> (flip App a <$> proceed e)
    Lam b e    -> testNWrap $ Lam b <$> proceed e
    Let b e    -> testNWrap $ Let b <$> proceed e
    Case{}     -> testNWrap unwrapFail
    Cast{}     -> testNWrap unwrapFail
    Tick t e   -> testNWrap $ Tick t <$> proceed e
    Type{}     -> unwrapFail
    Coercion{} -> unwrapFail
  where
    unwrapFail = pluginError
      $  "Failed to match a definition signature."
      $$ hang "Looking for a dictionary:" 2 (ppr dictT)
      $$ hang "Inspecting an expression:" 2
              (hsep [ppr ex, "::", ppr $ exprType ex])
    proceed = unwrapDictExpr dictT unwrapFun
    testNWrap go = if testType ex then wrap ex else go
    wrap e = flip fmap (getClsT e) $ \t -> Var unwrapFun `App` t `App` e
    -- type variables may differ, so I need to use tcMatchTy.
    -- I do not check if resulting substition is not trivial. Shall I?
    testType = isJust . tcMatchTy dictT . exprType
    getClsT e = case tyConAppArgs_maybe $ exprType e of
      Just [t] -> pure $ Type t
      _        -> unwrapFail
    mkThetaVar (i, ty) = newLocalVar ty ("theta" ++ show (i :: Int))
    mkLamApp =
      let et0          = exprType ex
          (bndrs, et1) = splitForAllTys et0
          (theta, _  ) = splitFunTysCompat et1
      in  if null bndrs && null theta
            then unwrapFail
            else do
              thetaVars <- traverse mkThetaVar $ zip [1 ..] theta
              let allVars      = bndrs ++ thetaVars
                  allApps      = map (Type . mkTyVarTy) bndrs ++ map Var thetaVars
                  fullyApplied = foldl App ex allApps
              return $ foldr Lam fullyApplied allVars


-- | Replace instance in ModGuts if its duplicate already exists there;
--   otherwise just add this instance.
replaceInstance :: ClsInst -> CoreBind -> ModGuts -> ModGuts
replaceInstance newI newB guts
  | NonRec _ newE <- newB
  , First (Just oldI) <- foldMap sameInst $ mg_insts guts
  , newDFunId <- instanceDFunId newI
  , origDFunId <- instanceDFunId oldI
  , dFunId <- newDFunId `setVarName`   idName origDFunId
                        `setVarUnique` varUnique origDFunId
  , bind   <- NonRec dFunId newE
  , inst   <- setClsInstDfunId dFunId newI
    = guts
      { mg_insts    = replInst origDFunId inst $ mg_insts guts
      , mg_inst_env = mg_inst_env guts
           `deleteFromInstEnv` oldI
           `extendInstEnv` inst
      , mg_binds    = bind : remBind origDFunId (mg_binds guts)
      }
  | otherwise
    = guts
      { mg_insts    = newI : mg_insts guts
      , mg_inst_env = extendInstEnv (mg_inst_env guts) newI
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
      | instanceDFunId i == d'   = i' : is
      | otherwise = i : replInst d' i' is
    sameInst i
      = First $ if identicalClsInstHead newI i then Just i else Nothing
