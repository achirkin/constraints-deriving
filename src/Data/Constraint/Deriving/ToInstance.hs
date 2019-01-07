{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
module Data.Constraint.Deriving.ToInstance
  ( ToInstance (..)
  , OverlapMode (..)
  , toInstancePass
  , CorePluginEnvRef, initCorePluginEnv
  ) where

import           Class               (Class, classTyCon)
import           Control.Applicative (Alternative (..))
import           Control.Monad       (join, unless)
import           Data.Data           (Data)
import           Data.Maybe          (fromMaybe, isJust)
import           Data.Monoid         (First (..))
import           GhcPlugins          hiding (OverlapMode (..), overlapMode)
import qualified InstEnv
import           Panic               (panicDoc)
import qualified Unify

import Data.Constraint.Deriving.CorePluginM


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

     * `fooNum` must be exported by the module
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
toInstancePass' gs = go (reverse $ mg_binds gs) annotateds gs { mg_binds = []}
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
            , mg_exports  = filterAvails (xn /=) $ mg_exports guts
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

toInstance (ToInstance omode) (NonRec bindVar bindExpr) = do
    -- check if all type arguments are constraint arguments
    unless (all (isConstraintKind . typeKind) theta) $
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
        instSig = mkSpecForAllTys bndrs $ mkFunTys theta matchedTy
        bindBareTy = mkSpecForAllTys bndrs $ mkFunTys theta $ mkTyConApp tcBareConstraint [matchedTy]

    -- check if constraint is indeed a class and get it
    matchedClass <- case tyConAppTyCon_maybe matchedTy >>= tyConClass_maybe of
      Nothing -> pluginLocatedError loc notGoodMsg
      Just cl -> pure cl

    -- try to apply dictToBare to the expression of the found binding
    newExpr <- case unwrapDictExpr dictTy fDictToBare bindExpr of
      Nothing -> pluginLocatedError loc notGoodMsg
      Just ex -> pure $ mkCast ex
                      $ mkUnsafeCo Representational bindBareTy instSig


    return $ mkNewInstance omode matchedClass bindVar newExpr

  where
    origBindTy = idType bindVar
    (bndrs, bindTy) = splitForAllTys origBindTy
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
