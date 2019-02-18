{-# LANGUAGE CPP         #-}
{-# LANGUAGE QuasiQuotes #-}
module Main (main) where

import DynFlags
import GHC
import GHC.Paths (libdir)
import Path
import Path.IO
#if __GLASGOW_HASKELL__ >= 802
import Util (OverridingBool (..))
#endif

-- | Folder with test modules to be compiled
specDir :: Path Rel Dir
specDir = [reldir|test/Spec/|]


main :: IO ()
main = do
  targetModules <- filter ((".hs" ==) . fileExtension) . snd <$> listDir specDir
  withSystemTempDir "constraints-deriving-tests" $ \outDir -> do
    r <- defaultErrorHandler defaultFatalMessager defaultFlushOut $
      runGhc (Just libdir) $ do
        dflags' <- makeSimpleAndFast <$> getSessionDynFlags
        (dflags, _, _) <- parseDynamicFlags dflags'
          [ noLoc "-Wall"
          , noLoc "-package ghc"
          , noLoc "-package constraints-deriving"
          , noLoc $ "-outputdir " ++ toFilePath outDir]
        _ <- setSessionDynFlags dflags
        traverse (flip guessTarget Nothing . toFilePath) targetModules >>= setTargets
        ghc800StaticFlagsFix
        load LoadAllTargets
    case r of
      Succeeded -> putStrLn "Done!"
      Failed    -> putStrLn "Oops!"


makeSimpleAndFast :: DynFlags -> DynFlags
makeSimpleAndFast flags = flags
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
    `gopt_set` Opt_ForceRecomp
    `gopt_unset` Opt_PrintUnicodeSyntax
#if __GLASGOW_HASKELL__ >= 802
    `gopt_unset` Opt_DiagnosticsShowCaret
#endif

ghc800StaticFlagsFix :: Ghc ()
#if __GLASGOW_HASKELL__ >= 802
ghc800StaticFlagsFix = return ()
#else
ghc800StaticFlagsFix = do
  decl <- parseImportDecl "import StaticFlags (initStaticOpts)"
  setContext [IIDecl decl]
  _ <- execStmt "initStaticOpts" execOptions
  return ()
#endif
