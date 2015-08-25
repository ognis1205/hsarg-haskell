-- * Implements translation between abstract and structured argumentation models.
-- | In the sense of IR theory, it would be more suitable that we take the abstract
--   model to retrieve informations, though, its algebra is weak for semantic analisys
--   so we implement translation between abstract and structured models.
module DSL.Translated.Api
    ( translate
    ) where

import Data.Graph.Inductive
import Data.List (delete)
import Data.Maybe
import DSL.Abstract.Api (Model(..))
import DSL.Structured.Api (Model(..), negate)
import DSL.Translated.Core
import DSL.Translated.Correspondence
import qualified DSL.Structured.Api as Structured
import qualified DSL.Translated.Core as Translated
import Prelude hiding (negate)

-- * "Translate"
-- | The function "translation" initialises the translation process by mapping all assumptions to arguments,
--   supplying the "translate'" with the initially acceptable arguments.
translate :: Structured.Model -> Translated.Model
translate smodel@(Strct (thrds, (asms, _), _)) =
    Abst (map snd args) (map clean atcks)
    where Abst args atcks = translate' (ordered thrds) smodel (Abst (truth : map convert asms) [])

translate' :: [(Structured.Proposition, [Structured.Argument])] -> Structured.Model -> Archetype -> Archetype
translate' []                           _                                    arch = arch
translate' (sprop@(prop, tfrs) : rems) smodel@(Strct (_, (asms, _), _)) (Abst args atcks)
    | prop `elem` asms = translate' rems smodel (Abst args atcks)
    | otherwise        = let ffrs            = falsifiabilities prop rems
                             (papp, patcks)  = translate_applicabilities args sprop
                             (capp, catcks)  = translate_applicabilities args ffrs
                             (pacc, patcks') = translate_acceptabilities prop papp capp smodel
                             (cacc, catcks') = translate_acceptabilities (negate prop) capp papp smodel
                             rems'           = delete ffrs rems
                         in  translate' rems' smodel (Abst (pacc : cacc : papp ++ capp ++ args) (patcks' ++ catcks' ++ patcks ++ catcks ++ atcks))
