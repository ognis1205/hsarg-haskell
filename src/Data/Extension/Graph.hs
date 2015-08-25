-- * Implements graph theoristic operators for the DynGraph type.
-- | The structured model requires that there are no cycles among dependencies. 
--   We use a dependency graph to determine acyclicity of a set of arguments.
module Data.Extension.Graph 
    ( cyclic
    ) where

import Data.Graph.Inductive

cyclic :: (DynGraph g) => g a b -> Bool
cyclic g | not (null leafs) = cyclic (delNodes leafs g)
         | otherwise        = not (isEmpty g)
         where leafs = filter (isLeaf g) (nodes g)

isLeaf :: (DynGraph g) => g a b -> Node -> Bool
isLeaf g n = n `notElem` map fst (edges g)
