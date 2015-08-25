-- * Implements set theoristic operators for the Ord type.
-- | Haskell Prelude "intersect", "(\\)" and "nub" implementations require an
--   Eq instance.
--   If we have an implementations for Ord type as well, the evaluation can be
--   sped up significantly.
module Data.Extension.Ord
    ( intersect
    , nub
    , subset
    , (\\)
    ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

intersect :: (Ord a) => [a] -> [a] -> [a]
intersect a b = filter (`Set.member` bset) a
    where bset = Set.fromList b

nub :: (Ord a) => [a] -> [a]
nub = nub' Set.empty
    where nub' _   []     = []
          nub' acc (x:xs) = if x `Set.member` acc
                            then nub' acc xs
                            else x : nub' (Set.insert x acc) xs

subset :: Ord a => [a] -> [a] -> Bool
x `subset` y = null (x \\ y)

infix 5 \\
(\\) :: (Ord a) => [a] -> [a] -> [a]
a \\ b = diff' init a
    where init = Map.fromListWith (+) [(x, 1 :: Int) | x <- b]
          diff' _    []     = []
          diff' hist (x:xs) = case Map.lookup x hist of
                                Just n | n > 0 -> diff' (Map.insert x (n - 1) hist) xs
                                _              -> x : diff' hist xs
