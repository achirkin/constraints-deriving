module Main (main) where

import Control.Monad (join)
import DynFlags
import GHC
import GHC.Paths     (libdir)
import Util          (OverridingBool (..))

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
            , useColor    = Never
            , canUseColor = False
            } `gopt_set` Opt_DoCoreLinting
              `gopt_unset` Opt_PrintUnicodeSyntax
              `gopt_unset` Opt_DiagnosticsShowCaret
          minusWall = join . map snd $ filter (("all"==) . fst) warningGroups
          fgs = foldl wopt_set fgs' minusWall
      _ <- setSessionDynFlags fgs
      target <- guessTarget "test/Spec/DeriveAll01.hs" Nothing
      setTargets [target]
      load LoadAllTargets
  case r of
    Succeeded -> putStrLn "Done!"
    Failed    -> putStrLn "Oops!"
