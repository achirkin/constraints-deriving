{-# LANGUAGE CPP                 #-}
module Main (main) where

import DynFlags
import GHC
import GHC.Paths     (libdir)
#if __GLASGOW_HASKELL__ >= 802
import Util          (OverridingBool (..))
#endif

main :: IO ()
main = do
  r <- defaultErrorHandler defaultFatalMessager defaultFlushOut $
    runGhc (Just libdir) $ do
      dflags <- getSessionDynFlags
      let fgs' = dflags
            { ghcMode     = OneShot
            , ghcLink     = NoLink
            , verbosity   = 1
            , optLevel    = 0
            , ways        = []
            , useUnicode  = False
#if __GLASGOW_HASKELL__ >= 802
            , useColor    = Never
            , canUseColor = False
#endif
            } `gopt_set` Opt_DoCoreLinting
              `gopt_unset` Opt_PrintUnicodeSyntax
#if __GLASGOW_HASKELL__ >= 802
              `gopt_unset` Opt_DiagnosticsShowCaret
#endif
              `gopt_set` Opt_ForceRecomp
              -- `dopt_set` Opt_D_dump_deriv
      (fgs, _, _) <- parseDynamicFlags fgs'
        [ noLoc "-Wall"
        , noLoc "-package ghc"
        , noLoc "-package constraints-deriving"]
      _ <- setSessionDynFlags fgs
      target <- guessTarget "test/Spec/DeriveAll01.hs" Nothing
      setTargets [target]
#if __GLASGOW_HASKELL__ < 802
      parseImportDecl "import StaticFlags (initStaticOpts)"
        >>= setContext . (:[]) . IIDecl
      _ <- execStmt "initStaticOpts" execOptions
#endif
      load LoadAllTargets
  case r of
    Succeeded -> putStrLn "Done!"
    Failed    -> putStrLn "Oops!"
