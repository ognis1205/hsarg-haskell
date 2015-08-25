-- * Implements an abstract argumentation model.
-- | Given an concrete Argument type, this module defines an abstract
--   argumentation model and its relating characteristic functions.
module DSL.Abstract.Core
    ( Model(..)
    , attacking
    , consistent
    , acceptable
    , admissible
    , acceptees
    , heads
    , attackers
    , tails
    , attackees
    , attacked
    , unattacked
    ) where

import Data.Extension.Ord (intersect, nub, subset, (\\))

-- * Abstract argumentation model.
-- | The model consists of the following axioms.
--   1. "Attackability"
--   2. "Consistability"
--   3. "Acceptability"
--   4. "Admissibility"
data Model arg = Abst [arg] [(arg, arg)] deriving (Show)

-- * "Attackability"
-- | A set S < Arguments is attacking x, iff, y <- S s.t. [y, x] <- Attacks.
attacking :: Eq arg => Model arg -> [arg] -> arg -> Bool
attacking (Abst _ atcks) args arg =
    or [y == arg | (x, y) <- atcks, x `elem` args]

-- * "Consistability"
-- | A set S < Arguments is called consistent, iff, there are no x, y in S s.t.
--   (x, y) <- Attacks.
consistent :: Eq arg => Model arg -> [arg] -> Bool
consistent (Abst _ atcks) args =
    null [(x, y) | (x, y) <- atcks, x `elem` args, y `elem` args]

-- * "Acceptability"
-- | A set S < Arguments accepts x, iff, for all arguments y <- Arguments:
--   if (y, x) <- Attacks then there exists z <- S for which (z, y) <- Attacks.
acceptable :: Eq arg => Model arg -> arg -> [arg] -> Bool
acceptable model@(Abst _ atcks) x args =
    and [attacking model args y | (y, x') <- atcks, x == x']

-- * "Admissibility"
-- | A consistent set of arguments S is admissible, iff, every argument x <- S
--   is scceptable with respect to S, i.e., S <- F_{mode} (S)
admissible :: Ord arg => Model arg -> [arg] -> Bool
admissible model args =
    consistent model args && args `subset` acceptees model args

-- * "Acceptees - Characteristic Function"
-- | The function "acceptees" of arguments with respect to the model, 
--   F_{model} : Arguments -> Arguments, is a function s.t. given a set of arguments S,
--   F_{model} (S) = {x | x is acceptable with respect to S}
acceptees :: Eq arg => Model arg -> [arg] -> [arg]
acceptees model@(Abst args' _) args =
    [x | x <- args', acceptable model x args]

-- * "Head Endpoints"
-- | The function "heads" of an argument with respect to the model, 
--   F_{Model} : Argument -> Arguments, is a function s.t. given an argument a,
--   F_{Model} (a) = {x | x is attacking a}
heads :: Eq arg => Model arg -> arg -> [arg]
heads (Abst _ atcks) arg =
    [x | (x, arg') <- atcks, arg == arg']

-- * "Attackers - Characteristic Function"
-- | The function "attackers" of arguments with respect to the model, 
--   F_{Model} : Arguments -> Arguments, is a function s.t. given arguments S,
--   F_{Model} (S) = {x | x is attacking a <- S}
attackers :: Ord arg => Model arg -> [arg] -> [arg]
attackers model =
    nub . concatMap (heads model)

-- * "Tail Endpoints"
-- | The function "tails" of an argument with respect to the model, 
--   F_{Model} : Argument -> Arguments, is a function s.t. given an argument a,
--   F_{Model} (a) = {x | x is attacked by a}
tails :: Eq arg => Model arg -> arg -> [arg]
tails (Abst _ atcks) arg =
    [x | (arg', x) <- atcks, arg == arg']

-- * "Attackees - Characteristic Function"
-- | The function "attackees" of arguments with respect to the model,
--   F_{Model} : Arguments -> Arguments, is a function s.t. given arguments S,
--   F_{Model} (S) = {x | x is attacked by a <- S}
attackees :: Ord arg => Model arg -> [arg] -> [arg]
attackees model =
    nub . concatMap (tails model)

-- * "Attacked"
-- | The function "attacked" of arguments with respect to the model,
--   given a list of arguments 'args', an argument 'arg' is attacked if there
--   exists an attacker that is args.
attacked :: Ord arg => [arg] -> Model arg -> arg -> Bool
attacked args (Abst _ atcks) arg =
    let atckrs = [x | (x, y) <- atcks, arg == y]
    in  not (null (atckrs `intersect` args))

-- * "Unattacked"
-- | The function "unattacked" of arguments with respect to the model,
--   given a list of arguments 'args', an argument 'arg' is unattacked if there
--   does not exist any attacker that is args.
unattacked :: Ord arg => [arg] -> Model arg -> arg -> Bool
unattacked args (Abst _ atcks) arg =
    let atckrs = [a | (a, b) <- atcks, arg == b]
    in  null (atckrs \\ args)
