-- * Defines argumentation theoristic operations for the structured model.
-- | Given an propositional literal type, this module defines an structured
--   argumentation model and its relating operators.
module DSL.Structured.Api
    ( threads
    , submit
    , validate
    , proposition
    , argument
    , applicabilities
    , inapplicabilities
    , acceptabilities
    , inacceptabilities
    , module DSL.Structured.Core
    , module DSL.Structured.Standard
    ) where

import Data.Graph.Inductive
import Data.Map (Map)
import qualified Data.Map as Map
import Prelude hiding (negate)
import Data.Extension.Graph
import DSL.Structured.Core
import DSL.Structured.Standard

-- * "Threads"
-- | The function "threads", given arguments, give back the dependency resolved
--   thread graph.
threads :: [Argument] -> Threads
threads = graphitize

-- * "Graphitize"
-- | The function "graphitize", given arguments, give back the dependency resolved
--   thread graph.
graphitize :: [Argument] -> ThreadGraph
graphitize =
    fst . foldr submit (empty, Map.empty)

-- * "Submit"
-- | The function "submit" with respect to the dependency, given an argument, insert
--   its conclusion into the dependency graph and resolve its relations.
submit :: Argument -> Dependency -> Dependency
submit arg@(Arg (prms, excs, cncl)) dep  = 
    let rels            = prms ++ excs
        ( dep',  cncl') = submit' arg dep
        (dep'', cncl'') = conclude (negate cncl) dep'
    in  associate cncl'' rels $ associate cncl' rels dep'' 

submit' :: Argument -> Dependency -> (Dependency, Conclusion)
submit' arg@(Arg (_, _, cncl)) (dep, tr) =
    case Map.lookup cncl tr of 
      Nothing    -> ((insNode (lab, (cncl, [arg])) dep, Map.insert cncl lab tr), lab)
      Just cncl' -> ((threadify arg (match' cncl' dep), tr), cncl')
    where lab = Map.size tr + 1

-- * "Validate"
-- | The function "validate", given an thread graph, validates if it is acyclic.
validate :: ThreadGraph -> Bool
validate = cyclic

-- * "Proposition"
-- | The function "proposition", given an proposition literal string, returns
--   correspondig Proposition instance with truth valeu.
proposition :: String -> Proposition
proposition ('-':s)  = mapFst not (proposition s)
proposition s        = (True, s)

-- * "Argument"
-- | The function "agenda", given propostion literals, instanciates the corresponding
--   argument.
argument :: [String] -> [String] -> String -> Argument
argument prms excs cncl =
    let proposition' = map proposition
    in  Arg (proposition' prms, proposition' excs, proposition cncl)

-- * "Applicabilities"
-- | The function "applicabilities" with respect to the model, given arguments, lists
--   up all applicable arguments within the threads.
applicabilities :: Model -> [Argument]
applicabilities model@(Strct (thds, _, _)) =
    filter (applicable model) (arguments thds)

-- * "Inapplicabilities"
-- | The function "inapplicabilities" with respect to the model, given arguments, lists
--   up all inapplicable arguments within the threads.
inapplicabilities :: Model -> [Argument]
inapplicabilities model@(Strct (thds, _, _)) =
    filter (not . (applicable model)) (arguments thds)

-- * "Applicabilities"
-- | The function "applicabilities" with respect to the model, given arguments, lists
--   up all applicable arguments within the threads.
acceptabilities :: Model -> [Proposition]
acceptabilities model@(Strct (thds, _, _)) =
    filter (acceptable model) (propositions thds)

inacceptabilities :: Model  -> [Proposition]
inacceptabilities model@(Strct (thds, _, _)) =
    filter (not . (acceptable model)) (propositions thds)
