-- * Implements correspondence of acceptability and applicability in structured model.
-- | This module defines translation of acceptability and applicability in the structured
--   model into the abstract one.
module DSL.Translated.Correspondence
    ( translate_applicabilities
    , translate_acceptabilities
    ) where

import DSL.Structured.Api (Argument(..), Model(..), Standard(..), negate, alpha, beta, gamma)
import qualified DSL.Structured.Api as Structured
import DSL.Translated.Core
import Data.Extension.Ord (intersect)
import Prelude hiding (negate)

-- * "Translated Applicabilities"
-- | The function "translate_applicabilities", takes two arguments a list of translated arguments
--    and a proposition paired with its to be translated arguments, collects the results of the 
--    "translate" function.
translate_applicabilities :: [Proposition]
                          -> (Structured.Proposition, [Structured.Argument])
                          -> ([Proposition], [(Proposition, Proposition)])
translate_applicabilities props (sprop, sargs) =
    let tr = map (translate props sprop) sargs
    in  (map fst tr, concatMap snd tr)

translate :: [Proposition] -> Structured.Proposition -> Structured.Argument -> (Proposition, [(Proposition, Proposition)])
translate props sprop arg@(Arg (prms, excs, cncl))
    | truths props `intersect` prms /= prms = ((False, Right arg), [(truth, (False, Right arg))])
    | otherwise                             =
        let excs' = truths' props excs
            arg'  = (null excs', Right arg)
            atcks = map (\ e -> (e, arg')) excs'
        in (arg', atcks)

-- * "Translated Acceptabilities"
-- | The functione "translate_aceptabilities", given a proposition, a list of pro arguments, a list of con arguments
--   and a structured model. The result will be an argument corresponding to the proposition and a list of attacks. 
translate_acceptabilities :: Structured.Proposition
                          -> [Proposition]
                          -> [Proposition]
                          -> Structured.Model
                          -> (Proposition, [(Proposition, Proposition)])
translate_acceptabilities sprop []                       ffrs smodel = ((False, Left sprop),  [(truth, (False, Left sprop))])
translate_acceptabilities sprop ((_, Left _) : tfrs)     ffrs smodel = error "proposition in list"
translate_acceptabilities sprop ((False, _)  : tfrs)     ffrs smodel = translate_acceptabilities sprop tfrs ffrs smodel
translate_acceptabilities sprop props@((True, _) : tfrs) ffrs smodel@(Strct (_, _, std))
    | std sprop == Scintilla                             = ((True, Left sprop), [])
    | std sprop == Preponderance && preponderating       = ((True, Left sprop), [])
    | std sprop == ClearAndConvincing && convincing      = ((True, Left sprop), []) 
    | std sprop == BeyondReasonableDoubt && beyond_doubt = ((True, Left sprop), [])
    | std sprop == DialecticalValidity && null ffrs      = ((True, Left sprop), [])
    | otherwise                                          = ((False, Left sprop), [(truth, (False, Left sprop))])
    where preponderating = likelyhood props smodel > likelyhood ffrs smodel
          convincing     = likelyhood props smodel > alpha
                           && likelyhood props smodel > likelyhood ffrs smodel + beta
          beyond_doubt   = likelyhood props smodel > alpha
                           && likelyhood props smodel > likelyhood ffrs smodel + beta
                           && likelyhood ffrs smodel < gamma

likelyhood :: [Proposition] -> Structured.Model -> Double
likelyhood prop smodel@(Strct (_, (_, importance), _)) =
    foldl max 0 [importance arg | (True, Right arg) <- prop] 
