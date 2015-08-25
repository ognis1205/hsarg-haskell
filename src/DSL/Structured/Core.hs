-- * Implements an argumentation dependency graph.
-- | In the structured argumentation model, the dependency graph of propositions
--   is the central part of the reasoning operations, so this module implements
--   the dependency graph.
module DSL.Structured.Core
    ( Proposition(..)
    , negate
    , Argument(..)
    , Threads(..)
    , Model(..)
    , Audience(..)
    , Assumptions(..)
    , Importance(..)
    , Weight(..)
    , Semantics(..)
    , Standard(..)
    , arguments
    , propositions
    , ThreadGraph(..)
    , ThreadNode(..)
    , Conclusion(..)
    , Dependency(..)
    , contexts
    , rationals
    , conclude
    , threadify
    , match'
    , associate
    ) where

import Data.Graph.Inductive
import Data.List (nub)
import Data.Map (Map)
import Data.Maybe (fromJust)
import Data.Extension.Graph
import qualified Data.Set as Set
import qualified Data.Map as Map
import Prelude hiding (negate)

-- * Represents logical formulae literals.
-- | All propositions are either positive or negative, so we defines propositions
--   as labelled strings.
type Proposition = (Bool, String)

-- * "Negate"
-- | The function "negate" of proposition negates the current value of the 
--   specified proposition.
negate :: Proposition -> Proposition
negate (b, x) = (not b, x)

-- * Argument type for Structured model.
-- | The argument consists of the following components:
--   1. "Premises"
--   2. "Exceptions"
--   3. "Conclusion"
newtype Argument = Arg ([Proposition], [Proposition], Proposition) deriving Ord

instance Eq Argument where
    (Arg (prms, excs, cncl)) == (Arg (prms', excs', cncl')) =
        Set.fromList prms == Set.fromList prms'
        && Set.fromList excs == Set.fromList excs'
        && cncl == cncl'

instance Show Argument where 
    show (Arg (prms, excs, (True, c))) =
        show (map show' prms) ++ ' ' : '~' : show (map show' excs) ++ "=>" ++ show c
    show (Arg (prms, excs, (_   , c))) =
        show (map show' prms) ++ ' ' : '~' : show (map show' excs) ++ "=>" ++ show ('-' : c)

show' :: Proposition -> String
show' (True, c) = c
show' (_   , c) = '-' : c

-- * Structured argumentation model.
-- | The structured argumentation model consists of the following components:
--   1. "Threads"
--   2. "Audience"
--   3. "Semantics"
newtype Model = Strct (Threads, Audience, Semantics)

-- * "Threads"
-- | Threads consists of conclusions with its relating arguments, which form
--   a dependency graph in according to the relating arguments' premises and
--   exceptions.
type Threads = Gr (Proposition, [Argument]) ()

-- * "Audience"
-- | An audience is a tuple of assumptions and weight.
type Audience = (Assumptions, Importance)

-- * "Assumptions"
-- | Asumptions is a propositionally consistent set of literals, i.e., not containing
--   both a literal and its negation.
type Assumptions = [Proposition]

-- * "Importance"
-- | An importance computes its importancy weights of propositions which is a member
--   of the assumptions.
type Importance = Argument -> Weight

-- * "Weight"
-- | An weight is a real value in the range [0, 1].
type Weight = Double

-- * Semantics.
-- | All propositions are either positive or negative, that means, each propositions
--   have model theoristic criterials, hence the semantics can be defined as a map
--   between propositions and its criterials.
type Semantics = Proposition -> Standard

-- * Standard.
-- | The propositions' standard consists of the following:
--   1. "Scintilla"
--   2. "Preponcerence"
--   3. "Clear and Convincing"
--   4. "Beyond Reasonable Doubt"
--   5. "Dialectical Validity"
data Standard = Scintilla
              | Preponderance
              | ClearAndConvincing
              | BeyondReasonableDoubt
              | DialecticalValidity
                deriving (Show, Eq)

-- * "Arguments"
-- | The function "arguments" with respect to the threads, given a threads, give
--   back the all arguments relating to the threads' conclusions.
arguments :: Threads -> [Argument]
arguments thds =
    nub $ concatMap (snd . snd) (labNodes thds)

-- * "Propositions"
-- | The function "propositions" with respect to the threads, given a threads, give
--   back the all propositions relating to the threads' conclusions.
propositions :: Threads -> [Proposition]
propositions thds =
    map (fst . snd) (labNodes thds)

-- * Thread Graph
-- | The structured argumentation model is based on graph operations, so we aliases
--   threads as a graph graph.
type ThreadGraph = Threads
type ThreadNode  = LNode (Proposition, [Argument])
type Conclusion  = Node

-- * Dependecy
-- | The dependency structure is defined as a pair of thread graph and map between
--   propositions and its node labels. This pairwise definition is just for the
--   implementation conveniency.
type Dependency = (ThreadGraph, Map Proposition Conclusion)

-- * "Contexts"
-- | The function "contexts" with respect to the thread graph, given a proposition 
--   and threads, give back the all contexts whose conclusion identifies to the given
--   proposition.
contexts :: Proposition -> ThreadGraph -> [Context (Proposition, [Argument]) ()]
contexts prop =
    gsel (\ (_, _, nd, _) -> fst nd == prop) 

-- * "Rationals"
-- | The function "rationals" with respect to the thread graph, given a proposition,
--   give back the all relations arguments whose conclusion identifies to the given
--   proposition.
rationals :: Proposition -> ThreadGraph -> [Argument]  
rationals prop gr =
    case contexts prop gr of
      []                          -> []
      ((_, _, (_, args), _) : _)  -> args

-- * "Conclude"
-- | The function "conclude" with respect to the dependency, given a proposition,
--   inserts the given proposition as an cnclusion without any associating arguments.
conclude :: Proposition -> Dependency -> (Dependency, Conclusion)
conclude prop dep@(gr, tr) =
    case Map.lookup prop tr of 
       Nothing -> ((insNode (lab, (prop, [])) gr, Map.insert prop lab tr), lab)
       Just n  -> (dep, n)
    where lab = Map.size tr + 1

-- * "Threadify"
-- | The function "threadify" with respect to the context, given an argument, inserts
--   the given argument as a thread to the context.
threadify :: Argument -> (Context (Proposition, [Argument]) (), ThreadGraph) -> ThreadGraph
threadify arg ((prcds, lab, (prop, args), sccs), g') =
    (prcds, lab, (prop, arg:args), sccs) & g'

-- * "Match'"
-- | The function "match'" with respect to the graph, given an node, finds the corresponding
--   nodes' contexts.
match' :: Graph gr => Node -> gr a b -> (Context a b, gr a b)
match' nd gr =
    mapFst fromJust $ match nd gr

-- * "Associate"
-- | The function "associate" with respect to the dependency, given a conclusion and a propositions,
--   generates edges between the conclusion and each depending propositions.
associate :: Conclusion -> [Proposition] -> Dependency -> Dependency
associate cncl props (gr, tr) =
    let lab    = Map.size tr + 1
        props' = filter ((== Nothing) . flip Map.lookup tr) props
        gr'    = insNodes (label props' lab) gr
        tr'    = Map.union tr . Map.fromList $ zip props' [lab..]
    in  associate' cncl (map (fromJust . flip Map.lookup tr') props) (gr', tr')

associate' :: Conclusion -> [Conclusion] -> Dependency -> Dependency
associate' cncl cncls (gr, tr) =
    let eds' = map (connect cncl) cncls
        connect nd nd' = (nd, nd', ())
    in  (insEdges eds' gr, tr)

label :: [Proposition] -> Conclusion -> [ThreadNode]
label props lab =
    zip [lab..] (map (\ prop -> (prop, [])) props)
