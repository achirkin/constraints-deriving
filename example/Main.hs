{-# LANGUAGE CPP       #-}
{-# LANGUAGE DataKinds #-}
module Main (main) where

#if __GLASGOW_HASKELL__ < 804
import           Data.Semigroup
#endif
import           Lib.Vector


main :: IO ()
main = do
    print $ Z <> (mempty :: Vector Double 0)
    print $ (7 :: Double) :* Z <> 15 :* Z
    print $ (7 :: Double) :* Z <> mempty 
    print $ mempty <> 2 :* 6 :* Z <> v2
    () <- case v2 of
      a :* as -> print $ a :* Z <> as
    print $ mempty <> 9 :* 8 :* 7 :* 6 :* 5 :* Z
                   <> 1 :* 2 :* 3 :* 4 :* 5 :* (Z :: Vector Double 0)
    case sdf2 of
      SomeVector x -> print $ mappend x x <> mempty
    case sdf7 of
      SomeVector x -> print $ x <> x <> x <> mempty <> x
  where
    -- The backend for v2 is known statically;
    -- GHC will pick up all instances for Vec2Base
    v2 = 3 :* 12 :* Z :: Vector Double 2
    -- The two vectors below hide their dimensionality until runtime.
    -- The only thing GHC knows is that they have instances of KnownBackend;
    -- thus, it will lookup the rest of required type class instances via KnownBackend route.
    sdf2 = SomeVector $ (2::Int) :* 6 :* Z
    sdf7 = SomeVector $ (1::Float)
      :* 2 :* 3 :* 4 :* 5 :* 16 :* 92 :* Z

