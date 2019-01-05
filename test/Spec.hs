{-# LANGUAGE CPP       #-}
{-# LANGUAGE DataKinds #-}
module Main (main) where

#if __GLASGOW_HASKELL__ < 804
import           Data.Semigroup
#endif
import           Lib.BackendFamily
import           Lib.Vector


main :: IO ()
main = do
    print $ Vec UnitBase <> (mempty :: Vector Double 0)
    print $ Vec (ScalarBase (7 :: Double)) <> Vec (ScalarBase 15)
    print $ Vec (ScalarBase (7 :: Double)) <> mempty
    print $ mempty <> Vec (Vec2Base 2 6) <> (Vec (Vec2Base 3 12) :: Vector Double 2)
    print $ mempty <> Vec (ListBase [9,8,7,6,5]) <> (Vec (ListBase [1,2,3,4,5]) :: Vector Double 5)
    case sdf2 of
      SomeVector x -> print $ mappend x x <> mempty
    case sdf7 of
      SomeVector x -> print $ f x
  where
    sdf2 = SomeVector $ Vec (Vec2Base 2 (6 :: Int))
    sdf7 = SomeVector
      (Vec (ListBase [1,2,3,4,5,16,92]) :: Vector Float 7)



f :: ( Semigroup t, Monoid t) => t -> t
f x = x <> x <> x <> mempty <> x
{-
 Pragma NOINLINE reduces the number of calls to the dictionary function.
 With optimization enabled, this is 6 vs 3.
 Assuming one call is for Show instance, f invokes the DFun  once for each type.

 If the function is inlined,  DFun seems to be invoked every time the Monoid
 or Semigroup functions are called.
 -}
{-# NOINLINE f #-}
