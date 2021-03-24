{-# LANGUAGE CPP #-}
#if __GLASGOW_HASKELL__ >= 900
{-# LANGUAGE PatternSynonyms #-}
#define CPP_GhcPlugins GHC.Plugins
#define CPP_InstEnv    GHC.Core.InstEnv
#define CPP_TyCoRep    GHC.Core.TyCo.Rep
#define CPP_ErrUtils   GHC.Utils.Error
#else
#define CPP_GhcPlugins GhcPlugins
#define CPP_InstEnv    InstEnv
#define CPP_TyCoRep    TyCoRep
#define CPP_ErrUtils   ErrUtils
#endif
module Data.Constraint.Deriving.Compat where

import CPP_GhcPlugins
    ( Id,DFunId, Type, Coercion, SrcSpan, SDoc
    , PrintUnqualified, Name, ModSummary, WarnReason
    , DynFlags, Role, UniqFM
    , splitFunTys, coreView, mkWildValBinder
    , mkLocalIdOrCoVar, mkLocalId, isBootSummary
    , mkUnivCo, typeKind
#if __GLASGOW_HASKELL__ >= 900
    , Mult, Unique, IsBootInterface(NotBoot)
    , pattern Many, irrelevantMult
#else
    , mkErrStyle
#if __GLASGOW_HASKELL__ >= 810
    , mkInvisFunTys
#endif
#endif
#if __GLASGOW_HASKELL__ >= 810
    , AnonArgFlag(..)
#else
    , splitFunTy_maybe, mkFunTys
#endif
#if __GLASGOW_HASKELL__ >= 806
    , tcIsConstraintKind
#else
    , Kind, HscEnv, Module, OccName
#endif
#if __GLASGOW_HASKELL__ >= 802
    , idName, putLogMsg
#else
    , Expr(..), TCvSubst, UniqSet
    , isCoercionTy_maybe, unicodeSyntax, char, flSelector, log_action
#endif
    )
import CPP_InstEnv (ClsInst(..))
import CPP_TyCoRep
    ( UnivCoProvenance(PluginProv)
#if __GLASGOW_HASKELL__ >= 810
    , Type (FunTy)
#endif
    , mkFunTy
    )
import CPP_ErrUtils (Severity)
#if __GLASGOW_HASKELL__ < 806
import Kind (isConstraintKind)
import IfaceEnv (lookupOrig)
import TcRnMonad (initTcForLookup)
#endif
#if __GLASGOW_HASKELL__ < 802
import Avail (AvailInfo(..))
import Unify (tcMatchTy)
#endif


#if __GLASGOW_HASKELL__ >= 900
type UniqMap = UniqFM Unique
#else
type UniqMap = UniqFM
#endif

#if __GLASGOW_HASKELL__ < 900
-- | A substitute for GHC.Core.Multiplicity that comes in GHC 9.0
data Mult = One | Many

mkInvisFunTysMany :: [Type] -> Type -> Type
#if __GLASGOW_HASKELL__ < 810
mkInvisFunTysMany = mkFunTys
#else
mkInvisFunTysMany = mkInvisFunTys
#endif
#endif

#if __GLASGOW_HASKELL__ < 810
data AnonArgFlag = VisArg | InvisArg
#endif

#if __GLASGOW_HASKELL__ < 802
uniqSetAny :: (a -> Bool) -> UniqSet a -> Bool
uniqSetAny g = foldl (\a -> (||) a . g) False

mkTyArg :: Type -> Expr b
mkTyArg ty
  | Just co <- isCoercionTy_maybe ty = Coercion co
  | otherwise                        = Type ty

bullet :: SDoc
bullet = unicodeSyntax (char '•') (char '*')

filterAvails :: (Name -> Bool) -> [AvailInfo] -> [AvailInfo]
filterAvails _    [] = []
filterAvails keep (a:as) = case go a of
    Nothing -> filterAvails keep as
    Just fa -> fa : filterAvails keep as
  where
    go x@(Avail _ n)
      | keep n    = Just x
      | otherwise = Nothing
    go (AvailTC n ns fs) =
      let ns' = filter keep ns
          fs' = filter (keep . flSelector) fs
      in if null ns' && null fs'
         then Nothing
         else Just $ AvailTC n ns' fs'

tcMatchTyKi :: Type -> Type -> Maybe TCvSubst
tcMatchTyKi = tcMatchTy
#endif

#if __GLASGOW_HASKELL__ < 806
lookupOrigIO :: HscEnv -> Module -> OccName -> IO Name
lookupOrigIO hscEnv m = initTcForLookup hscEnv . lookupOrig m

tcIsConstraintKind :: Kind -> Bool
tcIsConstraintKind = isConstraintKind
#endif

mkLocalIdCompat :: Name -> Mult -> Type -> Id
#if __GLASGOW_HASKELL__ >= 900
mkLocalIdCompat = mkLocalId
#else
mkLocalIdCompat name _ = mkLocalId name
#endif

mkLocalIdOrCoVarCompat :: Name -> Mult -> Type -> Id
#if __GLASGOW_HASKELL__ >= 900
mkLocalIdOrCoVarCompat = mkLocalIdOrCoVar
#else
mkLocalIdOrCoVarCompat name _ = mkLocalIdOrCoVar name
#endif


setClsInstDfunId :: DFunId -> ClsInst -> ClsInst
setClsInstDfunId dFunId i = i
  { is_dfun = dFunId
#if __GLASGOW_HASKELL__ >= 802
  , is_dfun_name = idName dFunId
#endif
  }

-- | Coercion with provenance given by the plugin
mkPluginCo :: String -> Role -> Type -> Type -> Coercion
mkPluginCo reason = mkUnivCo (PluginProv $ "constraints-deriving: " ++ reason)

mkFunTyCompat :: AnonArgFlag -> Mult -> Type -> Type -> Type
#if __GLASGOW_HASKELL__ >= 900
mkFunTyCompat = mkFunTy
#elif __GLASGOW_HASKELL__ >= 810
mkFunTyCompat f _ = mkFunTy f
#else
mkFunTyCompat _ _ = mkFunTy
#endif

splitFunTyCompat :: Type -> Maybe (AnonArgFlag, Mult, Type, Type)
#if __GLASGOW_HASKELL__ >= 900
splitFunTyCompat (FunTy vis mult arg res)
    = Just (vis, mult, arg, res)
#elif __GLASGOW_HASKELL__ >= 810
splitFunTyCompat (FunTy vis arg res)
    = Just (vis, Many, arg, res)
#else
splitFunTyCompat ty | Just (arg, res) <- splitFunTy_maybe ty
    = Just (mkConstraintInvis arg VisArg, Many, arg, res)
#endif
splitFunTyCompat ty | Just ty' <- coreView ty = splitFunTyCompat ty'
splitFunTyCompat _                            = Nothing


splitFunTysCompat :: Type -> ([Type], Type)
#if __GLASGOW_HASKELL__ >= 900
splitFunTysCompat t = (map irrelevantMult ts, r)
  where
    (ts, r) = splitFunTys t
#else
splitFunTysCompat = splitFunTys
#endif

-- | When you cannot decide if LHS of an arrow should be visible,
--   you can take this as a reasonable heuristic.
--   The second argument is the default visibility.
mkConstraintInvis :: Type -> AnonArgFlag -> AnonArgFlag
mkConstraintInvis arg vis = if tcIsConstraintKind (typeKind arg) then InvisArg else vis

mkWildValBinderCompat :: Type -> Id
#if __GLASGOW_HASKELL__ >= 900
mkWildValBinderCompat = mkWildValBinder Many
#else
mkWildValBinderCompat = mkWildValBinder
#endif

isNotBootFile :: ModSummary -> Bool
#if __GLASGOW_HASKELL__ >= 900
isNotBootFile = (NotBoot ==) . isBootSummary
#else
isNotBootFile = not . isBootSummary
#endif

putLogMsgCompat :: DynFlags -> WarnReason -> Severity
                -> SrcSpan -> PrintUnqualified -> SDoc -> IO ()
#if __GLASGOW_HASKELL__ >= 900
putLogMsgCompat df wr se ss _ = putLogMsg df wr se ss
#elif __GLASGOW_HASKELL__ >= 802
putLogMsgCompat df wr se ss pu = putLogMsg df wr se ss (mkErrStyle df pu)
#else
putLogMsgCompat df wr se ss pu = log_action df df wr se ss (mkErrStyle df pu)
#endif
