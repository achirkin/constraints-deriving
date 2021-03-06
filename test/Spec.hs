{-# LANGUAGE CPP               #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes       #-}
{-# LANGUAGE RecordWildCards   #-}
module Main (main) where

import           Control.Monad         (when, guard)
import           Data.ByteString       (ByteString)
import qualified Data.ByteString.Char8 as BS
import           Data.Char             (isSpace)
import           Data.Foldable         (fold)
import           Data.List             (sort)
import           Data.Maybe            (mapMaybe)
import           Data.Monoid
import           Data.Traversable      (for)
import           GHC
import           GHC.IO.Handle
import           GHC.Paths             (libdir)
import           Path
import           Path.IO
import           System.Exit
import           System.FilePath       (isPathSeparator)
import           System.IO
#if __GLASGOW_HASKELL__ >= 900
import           GHC.Driver.Session    ( LogAction, gopt_set, gopt_unset, defaultFatalMessager
                                       , defaultFlushOut, defaultLogActionHPrintDoc
                                       , defaultLogActionHPutStrDoc)
import           GHC.Utils.Error       (mkLocMessageAnn)
import           GHC.Utils.Monad       (liftIO)
import           GHC.Types.Name        (getOccString)
import           GHC.Utils.Outputable
#else
import           DynFlags              ( LogAction, gopt_set, gopt_unset, defaultFatalMessager
                                       , defaultFlushOut, defaultLogActionHPrintDoc
                                       , defaultLogActionHPutStrDoc)
import           ErrUtils              (mkLocMessageAnn)
import           MonadUtils            (liftIO)
import           Name                  (getOccString)
import           Outputable
#endif

replaceExt :: String -> Path b File -> Maybe (Path b File)
#if MIN_VERSION_path(0,7,0)
replaceExt = replaceExtension
#else
replaceExt = setFileExtension
#endif

removeExt :: Path b File -> Maybe (Path b File)
#if MIN_VERSION_path(0,7,0)
removeExt = fmap fst . splitExtension
#else
removeExt = setFileExtension ""
#endif

-- | Folder with test modules to be compiled
specDir :: Path Rel Dir
specDir = [reldir|test/Spec/|]

-- | Folder with expected compiler output dumps
outDir :: Path Rel Dir
outDir = [reldir|test/out/|]

correspondingStdOut :: Path a File -> Maybe (Path Rel File)
correspondingStdOut f = replaceExt ".stdout" $ outDir </> filename f

correspondingStdErr :: Path a File -> Maybe (Path Rel File)
correspondingStdErr f = replaceExt ".stderr" $ outDir </> filename f

data TargetPaths = TargetPaths
  { targetName :: String
  , targetPath :: FilePath
  , stdoutPath :: FilePath
  , stderrPath :: FilePath
  } deriving (Eq, Ord)

lookupTargetPaths :: Path a File -> Maybe TargetPaths
lookupTargetPaths p = do
#if MIN_VERSION_path(0,7,0)
  ext <- fileExtension p
#else
  let ext = fileExtension p
#endif
  guard $ ext == ".hs"
  targetPath <- Just $ toFilePath p
  targetName <- toFilePath <$> removeExt (filename p)
  stdoutPath <- toFilePath <$> correspondingStdOut p
  stderrPath <- toFilePath <$> correspondingStdErr p
  return TargetPaths {..}


main :: IO ()
main = do
  stdout' <- hDuplicate stdout
  stderr' <- hDuplicate stderr

  targetPaths <- sort . mapMaybe lookupTargetPaths <$>
    (listDir specDir >>= traverse makeRelativeToCurrentDir . snd)
  withSystemTempFile   "constraints-deriving-stdout" $ \_ outH ->
    withSystemTempFile "constraints-deriving-stderr" $ \_ errH ->
    withSystemTempDir  "constraints-deriving-tests"  $ \tempDir -> do
    r <- defaultErrorHandler defaultFatalMessager defaultFlushOut $
      runGhc (Just libdir) $ do
        dflags' <- makeSimpleAndFast <$> getSessionDynFlags
        (dflags, _, _) <- parseDynamicFlags dflags'
              { log_action = manualLogAction outH errH }
          [ noLoc "-Wall"
          , noLoc "-hide-all-packages"
          , noLoc "-package ghc"
          , noLoc "-package base"
          , noLoc "-package constraints-deriving"
          , noLoc "-dcore-lint"
          , noLoc $ "-outputdir " ++ toFilePath tempDir]
        _ <- setSessionDynFlags dflags
        ghc800StaticFlagsFix
        fmap fold $
          for targetPaths $ \TargetPaths{..} -> do
            -- compile the module
            target <- guessTarget targetPath Nothing
            setTargets [target]
            outPos <- liftIO $ hGetPosn outH
            errPos <- liftIO $ hGetPosn errH
            resCompile <- isSucceeded <$> load LoadAllTargets
            -- try to exec main function if it exists
            when (getAll resCompile) $ do
              modSystemIO <- parseImportDecl "import System.IO (hFlush, stderr, stdout)"
              modSumTarget <- getModSummary $ mkModuleName $ "Spec." ++ targetName
              setContext [IIDecl modSystemIO, IIModule $ moduleName  $ ms_mod modSumTarget]
              mainIsInScope <- any (("main" ==) . getOccString) <$> getNamesInScope
              when mainIsInScope $ do
                liftIO $ do
                  hDuplicateTo outH stdout
                  hDuplicateTo errH stderr
                _ <- execStmt "putStrLn \"\"" execOptions
                _ <- execStmt "putStrLn \"Output of running 'main':\"" execOptions
                r <- execStmt "main" execOptions
                _ <- execStmt "hFlush stdout" execOptions
                _ <- execStmt "hFlush stderr" execOptions
                liftIO $ do
                  case r of
                    ExecComplete { execResult = Left e } -> print e
                    _                                    -> return ()
                  hDuplicateTo stdout' stdout
                  hDuplicateTo stderr' stderr

            liftIO $ do
              -- flush logging handles to make sure logs are written
              hFlush outH
              hFlush errH
              hSetPosn outPos
              hSetPosn errPos
              -- compare logs against templates
              outExpectedBS <- trimBS <$> BS.readFile stdoutPath
              errExpectedBS <- trimBS <$> BS.readFile stderrPath
              sameOut <- getSameBytes outExpectedBS outH
                >>= reportSameBytes targetName "stdout" outExpectedBS
              sameErr <- getSameBytes errExpectedBS errH
                >>= reportSameBytes targetName "stderr" errExpectedBS
              let rez = fold [sameOut, sameErr, resCompile]
              when (rez == All True) $ do
                putStrLn ""
                putStrLn $ targetName ++ ": OK"
              return rez
    if getAll r
    then exitSuccess
    else exitFailure
  where
    isSucceeded Succeeded = All True
    isSucceeded Failed    = All False

    reportSameBytes _ _ _ SameBytes = pure $ All True
    reportSameBytes modN ch temBs (Different resBs) = do
      BS.putStrLn $ BS.unlines
        [ "", ""
        , "Failure testing module " `mappend` BS.pack modN `mappend` ":"
        , "  GHC " `mappend` ch `mappend` " does not match the expected output!"
        , ""
        , "---- Expected "  `mappend` ch `mappend` " -----------------------------"
        , temBs
        , "---- Content of " `mappend` ch `mappend` " ---------------------------"
        , resBs
        , "--------------------------------------------------"
        , ""
        ]
      return $ All False


data SameBytes = SameBytes | Different ByteString

-- | Read a ByteString from a handle and compare it to the template
--
--   Prerequisite: the template ByteString is trimmed (e.g. using trimBS)
getSameBytes :: ByteString -> Handle -> IO SameBytes
getSameBytes template handle =
    checkSame . trimBS <$> getAvailableBytes (max 1024 (BS.length template + 16))
  where
    checkSame bs
      | eqStar template bs = SameBytes
      | otherwise          = Different bs
    getAvailableBytes k = do
      bs <- BS.hGetNonBlocking handle k
      if BS.length bs < k
      then return bs
      else mappend bs <$> getAvailableBytes (k * 2)

-- | Eliminate whitespace characters on both sides of a ByteString
trimBS :: ByteString -> ByteString
trimBS = BS.map f . fst . BS.spanEnd isSpace . snd . BS.span isSpace
  where
    -- fix tests for Windows
    f c = if isPathSeparator c then '/' else c

-- | compare two ByteStrings such that the first can have wildcards '*'
eqStar :: ByteString -> ByteString -> Bool
eqStar template bs
      -- empty output
    | BS.null template = BS.null bs
      -- template allows anything
    | BS.all ('*' ==) template = True
      -- template starts with a wildcard
    | BS.null t1 = case BS.breakSubstring t21 bs of
        (_, bs')
          | BS.null bs' -> False
          | otherwise   -> eqStar t22
                         $ BS.drop (BS.length t21) bs'
      -- otherwise match prefix
    | otherwise = case BS.stripPrefix t1 bs of
        -- could not match
        Nothing  -> False
        -- could match a segment, continue
        Just bs' -> eqStar t2 bs'
  where
    (t1 , t2 ) = BS.span ('*' /=) template
    (t21, t22) = BS.span ('*' /=) $ BS.dropWhile ('*' ==) t2



makeSimpleAndFast :: DynFlags -> DynFlags
makeSimpleAndFast flags = flags
  { ghcMode     = CompManager
  , ghcLink     = LinkInMemory
  , hscTarget   = HscInterpreted
  , verbosity   = 1
  , optLevel    = 0
  , ways        = mempty
  , useUnicode  = False
  } `gopt_set` Opt_DoCoreLinting
    `gopt_set` Opt_ForceRecomp
    `gopt_unset` Opt_PrintUnicodeSyntax


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

-- | I've adapted the defaultLogAction from DynFlags with two goals in mind:
--
--   1. Make output as simple as possible (in particular, no utf-8)
--   2. Redirect stdout and stderr into dedicated handles
--
--   These all is to make testing output easy across different GHC versions.
manualLogAction :: Handle -> Handle -> LogAction
manualLogAction outH errH dflags _reason severity srcSpan
#if __GLASGOW_HASKELL__ < 900
  style
#endif
  msg
    = case severity of
      SevOutput      -> printOut msg
      SevDump        -> printOut (msg $$ blankLine)
      SevInteractive -> putStrSDoc msg
      SevInfo        -> printErrs msg
      SevFatal       -> printErrs msg
      SevWarning     -> printWarns
      SevError       -> printWarns
  where
    message = mkLocMessageAnn Nothing severity srcSpan msg
#if __GLASGOW_HASKELL__ >= 900
    printOut   = defaultLogActionHPrintDoc  dflags outH
    printErrs  = defaultLogActionHPrintDoc  dflags errH
    putStrSDoc = defaultLogActionHPutStrDoc dflags outH
    printWarns = hPutChar errH '\n' >> printErrs message
#else
    printOut   m = defaultLogActionHPrintDoc  dflags outH m style
    printErrs  m = defaultLogActionHPrintDoc  dflags errH m style
    putStrSDoc m = defaultLogActionHPutStrDoc dflags outH m style
    printWarns = do
      hPutChar errH '\n'
      defaultLogActionHPrintDoc dflags errH message
#if __GLASGOW_HASKELL__ >= 802
        (setStyleColoured False style)
#else
        style
#endif
#endif
