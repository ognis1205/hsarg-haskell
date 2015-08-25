-- * Implements proof standard and its relating operations.
-- | Given an concrete Argumentation model, this module defines an abstract
--   argumentation model and its relating characteristic functions.
module DSL.Structured.Standard
    ( Proof(..)
    , acceptable
    , applicable
    , alpha
    , beta
    , gamma
    ) where

import Prelude hiding (negate)
import DSL.Structured.Core

-- * Proof.
-- | The proof can be defined as actual implementations of the propositional
--   standard.
type Proof = Model -> Proposition -> Bool

-- * "Acceptability"
-- | The function "acceptable" of an argument with respect to the model,
--   given a propostion, returns true iff the corresponding proof standard
--   proves true.
acceptable :: Model -> Proposition -> Bool
acceptable model@(Strct (_, _, std)) prop=
    model `prove` prop
    where prove = proof $ std prop

proof :: Standard -> Proof 
proof Scintilla             = scintilla
proof Preponderance         = preponderance
proof ClearAndConvincing    = clear_and_convincing
proof BeyondReasonableDoubt = beyond_reasonable_doubt
proof DialecticalValidity   = dialectical_validity

-- * "Applicability"
-- | The function "applicable" of an argument with respect to the model,
--   given an argument, returns true iff:
--   1. for all its premimises which belongs to the assumptions, its negations
--      are not assumptions and acceptable to the model.
--   2. for all its exceptions which does not belong to the assumptions, its
--      negations are assumptions and and not acceptable to the model.
applicable :: Model -> Argument -> Bool
applicable model@(Strct (_, (asmps, _), _)) (Arg (prms, excs, _)) =
    let prms' = [prm `elem` asmps || (negate prm `notElem` asmps && acceptable model prm) | prm <- prms]
        excs' = [(exc `notElem` asmps) && (negate exc `elem` asmps || not (acceptable model exc)) | exc <- excs]
    in  and $ prms' ++ excs'

-- * "Scintilla"
-- | For a proposition to satisfy the weakest proof standard, scintilla of
--   evidence, there should be at least one applicable argument in the model.
scintilla :: Proof
scintilla model@(Strct (thds, _, _)) prop =
    any (applicable model) (rationals prop thds)

-- * "Preponderence"
-- | Preponderance of the evidence requires the maximum weight of the applicable
--   pro's arguments to be greater than the maximum weight of the applicable con's
--   arguments.
preponderance :: Proof
preponderance model prop =
    provability model prop > inprovability model prop

-- * "Clear and convincing"
-- | Clear and convincing requirs that the difference between the maximal weights
--   of the pro and con arguments must be greater than a given positive constant,
--   and there should be at least one applicable argument pro stronger than a given
--   positive constant.
clear_and_convincing :: Proof
clear_and_convincing model prop =
    let pro = provability model prop
        con = inprovability model prop
    in  (pro > alpha) && (pro - con > beta)

-- * "Beyond Reasonable Doubt"
-- | Beyond reasonable doubt has one further requirement, the maximal importance
--   of a con argument must be less than a given positive constant.
beyond_reasonable_doubt :: Proof
beyond_reasonable_doubt model prop =
    clear_and_convincing model prop && (inprovability model prop < gamma)

-- * "Dialectical Validity"
-- | Dialectical validity requires at least one applicable pro argument and no
--   applicable con arguments.
dialectical_validity :: Proof
dialectical_validity model prop =
    scintilla model prop && not (scintilla model (negate prop))

likelyhood :: Model -> [Argument] -> Weight
likelyhood model@(Strct (_, (_, importance), _)) args =
    foldl max 0 [importance arg | arg <- args, applicable model arg] 

provability :: Model -> Proposition -> Weight
provability model@(Strct (thds, _, _)) prop =
    likelyhood model (rationals prop thds)

inprovability :: Model -> Proposition -> Weight
inprovability model@(Strct (thds, _, _)) prop =
    likelyhood model (rationals (negate prop) thds)

alpha, beta, gamma :: Double
alpha  =  0.4
beta   =  0.3
gamma  =  0.2
