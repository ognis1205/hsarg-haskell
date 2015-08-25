-- * Implements fixpoint-operations and generation of cemplete extensions.
-- | Given an concrete Argumentation model, this module defines an abstract
--   argumentation model and its relating characteristic functions.
module DSL.Abstract.Fixpoint
    ( closure
    , closure'
    , completions'
    , preferabilities'
    , stabilities'
    ) where

import Data.List (delete)
import Data.Extension.Ord (subset, (\\))
import DSL.Abstract.Core

-- * "Closure"
-- | Given a function f, computes its closure, i.e., fixpoint.
closure :: Eq arg => ([arg] -> [arg]) -> [arg]
closure f =
    step f []
    where step f acc
              | f acc == acc = acc
              | otherwise    = step f acc

-- * "Closure'"
-- | Given a function f, computes its closure, i.e., fixpoint, strictly.
closure' :: Eq arg => ([arg] -> [arg]) -> [arg]
closure' f =
    step f []
    where step f acc
              | f acc == acc = acc
              | otherwise    = let acc' = f acc
                               in  acc' `seq` step f acc'

-- * "Completions'"
-- | Given an argumentation model, computes all complete extension.
--   The complete extension of a given model is defined as follows:
--   Ext_{model} = {S | S <- power(Arguments), S is admissible
--                                             & its aceeptees is itself}
completions' :: Ord arg => Model arg -> [[arg]]
completions' model@(Abst args _) =
    let f = acceptees model
        powerset :: [a] -> [[a]]
        powerset []     = [[]]
        powerset (x:xs) = powerset xs ++ map (x:) (powerset xs)
    in  filter (\ x -> admissible model x && x == f x) (powerset args)

-- * "Preferabilities'"
-- | Given an argumentation model, computes all preferred extensions.
--   The preferred extension of a given model is defined as follows:
--   Ext_{model} = {S | S <- completions'(Arguments), S is distinct}
preferabilities' :: Ord arg => Model arg -> [[arg]]
preferabilities' model@(Abst args _) =
    let cmps = completions' model
        preferred :: Ord arg => Model arg -> [[arg]] -> [arg] -> Bool
        preferred model exts ext = all (not . (ext `subset`)) (delete ext exts)
    in  filter (preferred model cmps) cmps

-- * "Stabilities'"
-- | Given an argumentation model, computes all stable extensions.
--   The stable extension of a given model is defined as follows:
--   Ext_{model} = {S | S <- preferabilities(Arguments), S is distinct}
stabilities' :: Ord arg => Model arg -> [[arg]]
stabilities' model@(Abst args _) =
    let prfs = preferabilities' model
        stable :: Ord arg => Model arg -> [arg] -> Bool 
        stable model@(Abst args _) exts = filter (unattacked (args \\ exts) model) args == exts
    in  filter (stable model) prfs
