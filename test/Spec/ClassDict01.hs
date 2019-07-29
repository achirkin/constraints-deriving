{-# OPTIONS_GHC -fplugin Data.Constraint.Deriving #-}
module Spec.ClassDict01 where

import           Data.Constraint
import           Data.Constraint.Deriving
import qualified Data.Monoid              as M

main :: IO ()
main = case testOrd of
  Dict -> do
    -- pattern-matching against Dict type makes `Ord Test` instance available
    -- within the scope of the case expression.
    print $ compare (Test 1 "hello") (Test 1 "world")
    print $ Test 2 "hello" > Test 1 "world"
    print $ max (Test 3 "A") (Test 3 "B")


-- Note, Test derives `Eq`, but not `Ord`
data Test = Test Int String
  deriving (Eq, Show, Read)

{-
Here I just use the function `defineOrd`.
In the source code, `defineOrd` is a dummy <<loop>> function,
but the GHC Core plugin replaces it with a proper implementation.
 -}
testOrd :: Dict (Ord Test)
testOrd = defineOrd
    cmp
    (\a b -> cmp a b == LT)
    (\a b -> cmp a b /= GT)
    (\a b -> cmp a b == GT)
    (\a b -> cmp a b /= LT)
    (\a b -> if cmp a b == LT then b else a)
    (\a b -> if cmp a b == GT then b else a)
  where
    cmp (Test i s) (Test j t) = compare i j M.<> compare s t

{-
This is where all the magic happens:

1. The ClassDict plugin pass picks up the `defineOrd` declaration
2. Checks the result type: `Dict (Ord a)`; infers the class of interest: `Ord`
3. Finds out the data constructor of the class `Ord` and compares it against the
   given function signature
4. If the types agree, the plugin replaces the generated GHC Core code with
   actual constructor (wrapped by `Dict`).

Note, the arguments of this function should be carefully translated from the
class declaration:
all superclasses go first, followed by all class methods (order matters!).
 -}
{-# ANN defineOrd ClassDict #-}
defineOrd :: Eq a                 -- Superclass
          => (a -> a -> Ordering) -- compare
          -> (a -> a -> Bool)     -- (<)
          -> (a -> a -> Bool)     -- (<=)
          -> (a -> a -> Bool)     -- (>)
          -> (a -> a -> Bool)     -- (>=)
          -> (a -> a -> a)        -- max
          -> (a -> a -> a)        -- min
          -> Dict (Ord a)
defineOrd = defineOrd
