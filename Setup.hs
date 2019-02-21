{-
Here is a very unfortunate hack that allows me to re-export modules of
the "constraints" library if flag "constraints" is enabled.

I have to do this because:

 * if flag "constraints" is disabled, the library exports its own modules
   (copied from the "constraints" library, thus the same API);

 * if I add reexported-modules in the package description, cabal check
   complains for duplicate modules
   (even though they are under mutually exclusive conditions);

 * I still want library users import the modules without PackageImports or alike
   independently of their choice of flags.
 -}
{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP #-}

#ifndef MIN_VERSION_Cabal
#define MIN_VERSION_Cabal(x,y,z) 0
#endif

module Main (main) where

import Distribution.PackageDescription
import Distribution.Simple
import qualified Distribution.ModuleName as ModuleName
#if MIN_VERSION_Cabal(2,0,0)
import Distribution.Types.CondTree (CondBranch(CondBranch))
#endif

main :: IO ()
main = defaultMainWithHooks simpleUserHooks
  { confHook = \(gpd, hbi) -> confHook simpleUserHooks (addReexportsGPD gpd, hbi) }

addReexportsGPD :: GenericPackageDescription -> GenericPackageDescription
addReexportsGPD gpd = gpd { condLibrary = addReexportsCT <$> condLibrary gpd }


addReexportsCT :: CondTree ConfVar [Dependency] Library
               -> CondTree ConfVar [Dependency] Library
addReexportsCT ct = ct
    { condTreeComponents = reexportBranch : condTreeComponents ct }
  where
    constraintsCondition = Var (Flag (mkFlagName "constraints"))
    reexportContent   = mempty
      { reexportedModules =
         [ ModuleReexport
             { moduleReexportOriginalPackage = Just (mkPackageName "constraints")
             , moduleReexportOriginalName = ModuleName.fromString "Data.Constraint"
             , moduleReexportName = ModuleName.fromString "Data.Constraint"
             }
         , ModuleReexport
             { moduleReexportOriginalPackage = Just (mkPackageName "constraints")
             , moduleReexportOriginalName = ModuleName.fromString "Data.Constraint.Unsafe"
             , moduleReexportName = ModuleName.fromString "Data.Constraint.Unsafe"
             }
         ]
      }
    constraintsTrueTree = CondNode
      { condTreeData        = reexportContent
      , condTreeConstraints = []
      , condTreeComponents  = []
      }
    constraintsFalseTree = Nothing
    reexportBranch =
#if MIN_VERSION_Cabal(2,0,0)
      CondBranch
#else
      (,,)
#endif
        constraintsCondition constraintsTrueTree constraintsFalseTree

#if !MIN_VERSION_Cabal(2,0,0)
mkFlagName :: String -> FlagName
mkFlagName = FlagName

mkPackageName :: String -> PackageName
mkPackageName = PackageName
#endif
