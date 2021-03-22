{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE OverloadedStrings  #-}
module Data.Constraint.Deriving.ClassDict
  ( ClassDict (..)
  , classDictPass
  , CorePluginEnvRef, initCorePluginEnv
  ) where

import           Control.Monad (join, unless, when)
import           Data.Data     (Data)
import           Data.Maybe    (fromMaybe, isJust)

import Data.Constraint.Deriving.CorePluginM
    ( Name,
      Outputable(ppr),
      getName,
      getUnique,
      mkTyArg,
      varsToCoreExprs,
      classDataCon,
      dataConWorkId,
      idType,
      mkCoreConApps,
      mkCoreLams,
      nameSrcSpan,
      ($$),
      ($+$),
      bullet,
      hcat,
      hsep,
      speakN,
      vcat,
      tyConClass_maybe,
      tyConSingleDataCon,
      mkTyConApp,
      splitForAllTys,
      splitTyConApp_maybe,
      delFromUFM,
      eltsUFM,
      isNullUFM,
      lookupUFM,
      CoreToDo(CoreDoPluginPass),
      Bind(Rec, NonRec),
      CoreBind,
      CoreBndr,
      CoreExpr,
      ModGuts(mg_binds),
      occName,
      UniqFM,
      typesCantMatch,
      CorePluginEnv(tyConDict),
      CorePluginEnvRef,
      CorePluginM,
      runCorePluginM,
      try,
      ask,
      initCorePluginEnv,
      newLocalVar,
      pluginLocatedError,
      pluginWarning,
      pluginLocatedWarning,
      getModuleAnns,
      splitFunTysUnscaled,
      mapResultType )


{- | A marker to tell the core plugin to replace the implementation of a
     top-level function by a corresponding class data constructor
       (wrapped into `Data.Constraint.Dict`).

     Example:

@

class BarClass a => FooClass a where
  fooFun1 :: a -> a -> Int
  fooFun2 :: a -> Bool

{\-\# ANN deriveFooClass ClassDict \#-\}
deriveFooClass :: forall a . BarClass a
               => (a -> a -> Int)
               -> (a -> Bool)
               -> Dict (FooClass a)
deriveFooClass = deriveFooClass
@

     That is, the plugin replaces the RHS of @deriveFooClass@ function with
     `DataCon.classDataCon` wrapped by `bareToDict`.

     Note:

     * The plugin requires you to create a dummy function `deriveFooClass` and
       annotate it with `ClassDict` instead of automatically creating this function
       for you; this way, the function is visible during type checking:
       you can use it in the same module (avoiding orphans) and you see its type signature.
     * You have to provide a correct signature for `deriveFooClass` function;
       the plugin compares this signature against visible classes and their constructors.
       An incorrect signature will result in a compile-time error.
     * The dummy implementation @deriveFooClass = deriveFooClass@ is used here to
       prevent GHC from inlining the function before the plugin can replace it.
       But you can implement in any way you like at your own risk.
 -}
data ClassDict = ClassDict
  deriving (Eq, Show, Read, Data)

-- | Run `ClassDict` plugin pass
classDictPass :: CorePluginEnvRef -> CoreToDo
classDictPass eref = CoreDoPluginPass "Data.Constraint.Deriving.ClassDict"
  -- if a plugin pass totally  fails to do anything useful,
  -- copy original ModGuts as its output, so that next passes can do their jobs.
  (\x -> fromMaybe x <$> runCorePluginM (classDictPass' x) eref)

classDictPass' :: ModGuts -> CorePluginM ModGuts
classDictPass' guts = do
    (remAnns, processedBinds) <- runWithAnns (traverse go (mg_binds guts)) annotateds
    unless (isNullUFM remAnns) $
      pluginWarning $ "One or more ClassDict annotations are ignored:"
        $+$ vcat
          (map pprBulletNameLoc . join $ eltsUFM remAnns)
        $$ "Note possible issues:"
        $$ pprNotes
         [ "ClassDict is meant to be used only on bindings of type Ctx => Dict (Class t1 .. tn)."
         , "GHC may remove the annotated definition if it is not reachable from module exports."
         ]
    return guts { mg_binds = processedBinds}
  where
    annotateds :: UniqFM [Name]
    annotateds = map fst <$> (getModuleAnns guts :: UniqFM [(Name, ClassDict)])

    go :: CoreBind -> WithAnns CoreBind
    go (NonRec b e) = NonRec b <$> classDict' b e
    go (Rec bes)    = Rec <$> traverse (\(b, e) -> (,) b <$> classDict' b e) bes

    pprBulletNameLoc n = hsep
      [" " , bullet, ppr $ occName n, ppr $ nameSrcSpan n]
    pprNotes = vcat . map (\x -> hsep [" ", bullet, x])

    classDict' x origBind = WithAnns $ \anns -> case lookupUFM anns (getUnique x) of
      Just (xn:xns) -> do
        unless (null xns) $
          pluginLocatedWarning (nameSrcSpan xn) $
            "Ignoring redundant ClassDict annotations" $$
            hcat
            [ "(the plugin needs only one annotation per binding, but got "
            , speakN (length xns + 1)
            , ")"
            ]
        -- add new definitions and continue
        (,) (delFromUFM anns (getUnique x))  . fromMaybe origBind <$> try (classDict x)
      _ -> return (anns, origBind)

-- a small state transformer for tracking remaining annotations
newtype WithAnns a = WithAnns
  { runWithAnns :: UniqFM [Name] -> CorePluginM (UniqFM [Name], a) }

instance Functor WithAnns where
  fmap f m = WithAnns $ fmap (fmap f) . runWithAnns m

instance Applicative WithAnns where
  pure x = WithAnns $ \anns -> pure (anns, x)
  mf <*> mx = WithAnns $ \anns0 -> do
    (anns1, f) <- runWithAnns mf anns0
    (anns2, x) <- runWithAnns mx anns1
    pure (anns2, f x)


-- | Replace a given CoreBind with a corresponding class DataCon fun implementation.
--
--   The core bind must have type `Ctx => Dict (Class t1 .. tn)`;
--   it does not change.
classDict :: CoreBndr -> CorePluginM CoreExpr

classDict bindVar = do

    -- get necessary definitions
    tcDict <- ask tyConDict
    let conDict = tyConSingleDataCon tcDict

    -- check that the outermost constructor of the result type is Dict
    -- and unwrap it.
    dictContentTy <- case splitTyConApp_maybe dictTy of
      Just (tcDict', [resTy])
        | tcDict' == tcDict -> pure resTy
      err -> pluginLocatedError loc $ vcat
        [ hsep
          [ "Expected `Dict (Cls t1..tn)', but found", ppr dictTy]
        , if isJust err
          then "(constructor or number of arguments do not match)."
          else "(I could not split apart a constructor application)."
        , notGoodMsg
        ]

    -- check if the content of the result Dict is indeed a class constraint
    -- and get the class and its arguments.
    (klass, instanceArgs) <- case splitTyConApp_maybe dictContentTy of
      Just (klassTyCon, iArgs)
        | Just klas <- tyConClass_maybe klassTyCon
          -> pure (klas, iArgs)
        | otherwise
          -> pluginLocatedError loc $ vcat
            [ hsep
              [ "Expected a class constructor, but found", ppr klassTyCon]
            ,   "(not a class data constructor)."
            , notGoodMsg
            ]
      Nothing -> pluginLocatedError loc $ vcat
            [ hsep
              [ "Expected a class constructor, but found", ppr dictContentTy]
            ,   "(I could not split apart a constructor application)."
            , notGoodMsg
            ]

    -- the core of the plugin: use a class data constructor
    let klassDataCon = classDataCon klass

    -- check if the types agree
    let expectedType = mapResultType (mkTyConApp tcDict . (:[]))
                       . idType $ dataConWorkId klassDataCon

    when (typesCantMatch [(origBindTy, expectedType)]) $
      pluginLocatedError loc $ vcat
            [ hsep
              [ "Cannot match the expected type (the type of the data constructor of the given class)"
              , "and the found type (the user-supplied binding)."]
            , hsep ["Expected type:", ppr expectedType]
            , hsep ["Found type:   ", ppr origBindTy]
            ]

    argVars <- traverse (`newLocalVar` "t") argTys
    return
      . mkCoreLams (bndrs ++ argVars)
      $ mkCoreConApps conDict
        [ mkTyArg dictContentTy
        , klassDataCon `mkCoreConApps`
          (map mkTyArg instanceArgs ++ varsToCoreExprs argVars)
        ]

  where
    origBindTy = idType bindVar
    (bndrs, bindTy) = splitForAllTys origBindTy
    (argTys, dictTy) = splitFunTysUnscaled bindTy
    loc = nameSrcSpan $ getName bindVar
    notGoodMsg =
         "ClassDict plugin pass failed to process a Dict declaraion."
      $$ "The declaration must have form `forall a1..an . Ctx => Dict (Cls t1..tn)'"
      $$ "Declaration:"
      $$ hcat
         [ "  "
         , ppr bindVar, " :: "
         , ppr origBindTy
         ]
