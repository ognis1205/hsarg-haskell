-- * Implements translation between abstract and structured argumentation models.
-- | In the sense of IR theory, it would be more suitable that we take the abstract
--   model to retrieve informations, though, its algebra is weak for semantic analisys
--   so we implement translation between abstract and structured models.
module DSL.Translated.Core
    ( Literal(..)
    , Proposition(..)
    , Model(..)
    , Archetype(..)
    , truth
    , ordered
    , convert
    , clean
    , falsifiabilities
    , truths
    , truths'
    , leftify
    , rightify
    ) where

import Data.Graph.Inductive
import Data.List (find)  
import Data.Maybe
import DSL.Structured.Api (proposition, validate, negate)
import qualified DSL.Abstract.Api as Abstract
import qualified DSL.Structured.Api as Structured
import Prelude hiding (negate)

-- * Translated abstract argumentation model.
-- | The resulting model includes propositions corresponding to the structured-model's arguments,
--   however, it also includes propositions representing structured model's propositions.
type Literal     = Either Structured.Proposition Structured.Argument
type Proposition = (Bool, Literal)
type Model       = Abstract.Model Literal
type Archetype   = Abstract.Model Proposition

-- * Truth.
-- | One additional argument called |truth|. This is added to the abstruct model
--   as an unattacked argument and will attack other arguments that do not satisfy
--   their assigned proof standard in the sense of structured model.
truth :: Proposition
truth = (True, Left $ proposition "truth")

-- * "Ordered"
-- | The function "ordered" with respect to the threads, given a threads, give
--   back the topologically ordered threads' list.
ordered :: Structured.Threads -> [(Structured.Proposition, [Structured.Argument])]
ordered thds | validate thds  = error "thread graph is cyclic"
             | otherwise                 = reverse (topsort' thds)

-- * "Convert"
-- | The function "convert", given a structured proposition, converts its corresponding
--   translated proposition.
convert :: Structured.Proposition -> Proposition
convert sprop = (True, Left sprop)

-- * "Clean"
-- | The function "clean", given a paired propositions, stripes out its labels.
clean :: (Proposition, Proposition) -> (Literal, Literal) 
clean (prop, prop') = (snd prop, snd prop')

-- * "Falisifiabilities"
-- | The function "falsiabilities", given a paired propositions, stripes out its labels.
falsifiabilities :: Structured.Proposition -> [(Structured.Proposition, [Structured.Argument])] -> (Structured.Proposition, [Structured.Argument])
falsifiabilities sprop args =
    maybe ((negate sprop), []) id (find ((== (negate sprop)) . fst) args)

-- * "Truths"
-- | The function "truths", given propositions, returns all true structured propositions
--   among them.
truths :: [Proposition] -> [Structured.Proposition]
truths []                         = []
truths ((True,  Left  sprop) : props) = sprop : truths props
truths ((True,  Right _    ) : props) = truths props
truths ((False, _          ) : props) = truths props

-- * "Truths'"
-- | The function "truths'", given propositions, returns all true structured propositions
--   within them.
truths' :: [Proposition] -> [Structured.Proposition] -> [Proposition]
truths' props excs =
    filter (\ (b, arg) -> b && either (\e -> e `elem` excs) (const False) arg) props
          
leftify []               = []
leftify ((Left x) : xs)  = x : leftify xs
leftify (_ : xs)         = leftify xs

rightify []               = []
rightify ((Right x) : xs) = x : rightify xs
rightify (_ : xs)         = rightify xs
