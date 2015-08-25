-- * Defines argumentation theoristic operations for the abstract model.
-- | Given an concrete Argumentation model, this module defines an abstract
--   argumentation model and its relating operators.
module DSL.Abstract.Api
    ( Status(..)
    , Context(..)
    , cogents
    , incogents
    , uncertains
    , cogentify
    , incogentify
    , uncertainify
    , possibilities
    , verify
    , consensus
    , cogentifiable
    , incogentifiable
    , certainifiable
    , cogent
    , incogent
    , uncertain
    , contradictive
    , sound
    , complete
    , grounded
    , preferred
    , stable
    , semistable
    , completions
    , preferabilities
    , stabilities
    , semistabilities
    , expand
    , module DSL.Abstract.Core
    , module DSL.Abstract.Fixpoint
    ) where

import Data.List (partition, delete, sort)
import Data.Extension.Ord (nub, subset, (\\))
import DSL.Abstract.Core
import DSL.Abstract.Fixpoint

-- * Specifies a given argument is cogent or not.
-- | A given argument's status can be one of the followings:
--   1. "Cogent"
--   2. "Incogent"
--   3. "Uncertain"
data Status = Cogent | Incogent | Uncertain deriving (Eq, Show, Ord)

-- * Abstract argumentation theorestic frameworks' context.
-- | A context of the framework consists of arguments which is labelled
--   with the above status.
type Context arg = [(arg, Status)]

-- * "Cogents"
-- | The function "cogents" of arguments with respect to the context,
--   given a context, give back the arguments labelled 'Cogent'.
cogents :: Context arg -> [arg]
cogents cxt =
    [x | (x, Cogent) <- cxt]

-- * "Incogents"
-- | The function "incogents" of arguments with respect to the context,
--   given a context, give back the arguments labelled 'Incogent'.
incogents :: Context arg -> [arg]
incogents cxt =
    [x | (x, Incogent) <- cxt]

-- * "Uncertains"
-- | The function "uncertains" of arguments with respect to the context,
--   given a context, give back the arguments labelled 'Uncertain'.
uncertains :: Context arg -> [arg]
uncertains cxt =
    [x | (x, Uncertain) <- cxt]

-- * "Cogentify"
-- | The function "cogentify" of arguments lebels every argument 'Cogent'.
cogentify :: [arg] -> Context arg
cogentify =
    map (\ x -> (x, Cogent))

-- * "Incogentify"
-- | The function "incogentify" of arguments lebels every argument 'Incogent'.
incogentify :: [arg] -> Context arg
incogentify =
    map (\ x -> (x, Incogent))

-- * "Uncertainify"
-- | The function "uncertainify" of arguments lebels every argument 'Uncertain'.
uncertainify :: [arg] -> Context arg
uncertainify =
    map (\ x -> (x, Uncertain))

-- * "Possibilities"
-- | The function "possibilities" of arguments lists all possible labellings.
possibilities :: [arg] -> [Context arg]
possibilities []     = [[]]
possibilities (x:xs) =
    map ((x, Cogent):)       (possibilities xs)
    ++ map ((x, Incogent):)  (possibilities xs)
    ++ map ((x, Uncertain):) (possibilities xs)

-- * "Verify"
-- | Computes the verified context for an abstract argumentation model,
--   returning a (unique) list of arguments with statuses.
verify :: Ord arg => Model arg -> Context arg
verify model@(Abst args _) =
    verify' [] [] args model
    where 
      verify' :: Ord a => [a] -> [a] -> [a] -> Model a -> [(a, Status)]
      verify' cgts icgts []   _     =
          cogentify cgts ++ incogentify icgts
      verify' cgts icgts args model =
          let cgts'  = filter (unattacked icgts model) args
              icgts' = filter (attacked   cgts  model) args
              args'  = args \\ (cgts' ++ icgts')
          in  if null (cgts' ++ icgts')
              then cogentify cgts ++ incogentify icgts ++ uncertainify args
              else verify' (cgts ++ cgts') (icgts ++ icgts') args' model

-- * "Consensus"
-- | The verified extension, i.e., consensus of an argumentation model is
--   just the verified labelling, keeping only those arguments that were
--   labelled 'Cogent'.
consensus :: Ord arg => Model arg -> [arg]
consensus model =
    [x | (x, Cogent) <- verify model] 

-- * "Counters"
-- | Given an argumentation model, determines the list of attackers of an argument, 
--   from a given labelling, returning the labelled attackers. 
counters :: Eq arg => Model arg -> arg -> Context arg -> Context arg
counters (Abst args atcks) a cxt =
    [lab | lab@(b, _) <- cxt, (b, a) `elem` atcks]

-- * "Congentifiable"
-- | Given an argumentation model and context,
--   an argument a is 'congentifiable' iff a is labelled 'Incogent', but does not
--   have an attacker labelled 'Cogent'.
cogentifiable :: Eq arg => Model arg -> Context arg -> (arg, Status) -> Bool
cogentifiable _     _   (_, Cogent)    = False
cogentifiable _     _   (_, Uncertain) = False
cogentifiable model cxt (a, Incogent)  =
    null [lab | lab@(_, Cogent) <- counters model a cxt]

-- * "Incongentifiable"
-- | Given an argumentation model and context,
--   an argument a is 'incongentifiable' iff a is labelled 'Cogent', but not all
--   its attackers are labelled 'Incogent'.
incogentifiable :: Eq arg => Model arg -> Context arg -> (arg, Status) -> Bool
incogentifiable _     _   (_, Incogent)  = False
incogentifiable _     _   (_, Uncertain) = False
incogentifiable model cxt (a, Cogent) =
    not . null $ [lab | lab@(_, stat) <- counters model a cxt, stat /= Incogent]

-- * "Certainifiable"
-- | Given an argumentation model and context,
--   an argument a is 'certainifiable' iff a is labelled 'Uncertain' but either
--   all its attackers are labelled 'Incogent' or it has an attacker that is
--   labelled 'Cogent'.
certainifiable :: Eq arg => Model arg -> Context arg -> (arg, Status) -> Bool
certainifiable _     _   (_, Cogent)    = False
certainifiable _     _   (_, Incogent)  = False
certainifiable model cxt (a, Uncertain) =
    and [stat == Incogent | (_, stat) <- counters model a cxt]
    || (not . null) [lab | lab@(_, Cogent) <- counters model a cxt]

-- * "Cogent"
-- | Given an argumentation model and context,
--   an argument a is surely 'Cogent' iff a is labelled 'Cogent' and it's not
--   'incogentifiable'.
cogent :: Eq arg => Model arg -> Context arg -> (arg, Status) -> Bool
cogent _     _       (_, Incogent)  = False
cogent _     _       (_, Uncertain) = False
cogent model cxt arg@(_, Cogent)    =
    not $ incogentifiable model cxt arg

-- * "Incogent"
-- | Given an argumentation model and context,
--   an argument a is surely 'Incogent' iff a is labelled 'Incogent' and it's not
--   'cogentifiable'.
incogent :: Eq arg => Model arg -> Context arg -> (arg, Status) -> Bool
incogent _     _       (_, Cogent)    = False
incogent _     _       (_, Uncertain) = False
incogent model cxt arg@(_, Incogent)  =
    not $ cogentifiable model cxt arg

-- * "Uncertain"
-- | Given an argumentation model and context,
--   an argument a is surely 'uncertain' iff a is labelled 'Uncertain' and it's not
--   'certainifiable'.
uncertain :: Eq arg => Model arg -> Context arg -> (arg, Status) -> Bool
uncertain _     _       (_, Cogent)    = False
uncertain _     _       (_, Incogent)  = False
uncertain model cxt arg@(_, Uncertain) =
    not $ certainifiable model cxt arg

-- * "Contradictive"
-- | Given an argumentation model and context,
--   an argument a is 'contradictive' iff a is labelled 'Cogent', and it is attacked
--   by an argument that is surely 'Cogent' or surely 'Uncertain'.
contradictive :: Eq arg => Model arg -> Context arg -> (arg, Status) -> Bool
contradictive _     _   (_, Incogent)  = False
contradictive _     _   (_, Uncertain) = False
contradictive model cxt (a, Cogent)    =
    let ctrs = [lab | lab <- counters model a cxt, cogent model cxt lab || uncertain model cxt lab]
    in  not . null $ ctrs

-- * "Sound"
-- | Given an argumentation model abd context,
--   an sound labelling is a 'Labelling' without arguments that are 'incogentifiable'
--   and without arguments that are 'cogentifiable'.
sound :: Eq arg => Model arg -> Context arg -> Bool
sound model cxt =
    let cgts  = [lab | lab@(a, Cogent)   <- cxt, incogentifiable model cxt lab]
        icgts = [lab | lab@(a, Incogent) <- cxt,   cogentifiable model cxt lab] 
    in  null $ cgts ++ icgts

-- * "Complete"
-- | Given an argumentation model abd context,
--   a complete labelling is a labelling without arguments that are 'incogentifiable',
--   without arguments that are 'cogentifiable' and without arguments that are
--   'certainifiable'.
complete ::  Eq arg => Model arg -> Context arg -> Bool
complete model cxt =
    let cgts  = [lab | lab@(a, Cogent)    <- cxt, incogentifiable model cxt lab]
        icgts = [lab | lab@(a, Incogent)  <- cxt,   cogentifiable model cxt lab] 
        uctns = [lab | lab@(a, Uncertain) <- cxt,  certainifiable model cxt lab] 
    in  null $ cgts ++ icgts ++ uctns

-- * "Grounded"
-- | Let cxt be a complete context, i.e., @complete model cxt@, we say that cxt is
--   a grounded context iff it is the minimal context for all possible contexts with
--   respect to the cogents-set inclusion.
grounded :: Ord arg => Model arg -> [Context arg] -> Context arg -> Bool
grounded model cxts cxt =
    let verified = subset (cogents cxt)
    in  complete model cxt && all verified (map cogents cxts)

-- * "Preferred"
-- | Let cxt be a complete context, i.e., @complete model cxt@, we say that cxt is
--   a preferred context iff it is the maximal context for all possible contexts with
--   respect to the congents-set inclusion.
preferred :: Ord arg => Model arg -> [Context arg] -> Context arg -> Bool
preferred model cxts cxt =
    let verified = not . (subset (cogents cxt))
    in  complete model cxt && all verified (map cogents (delete cxt cxts))

-- * "Stable"
-- | Let cxt be a complete context, i.e., @complete model cxt@, we say that cxt is
--   a stable context iff there does not exist any 'Uncertain' labelling.
stable :: Eq arg => Model arg -> [Context arg] -> Context arg -> Bool
stable model cxts cxt =
    complete model cxt && null (uncertains cxt)

-- * "Semi-stable"
-- | Let cxt be a complete context, i.e., @complete model cxt@, we say that cxt is
--   a semi-stable context iff it is the minimal context for all possible contexts with
--   respect to the uncertains-set inclusion.
semistable :: Ord arg => Model arg -> [Context arg] -> Context arg -> Bool
semistable model cxts cxt =
    let verified = subset (uncertains cxt)
    in  complete model cxt && all verified (map uncertains cxts)

-- * "Completions"
-- | Computes maximal and minimal complete labellings for the abstract  model.
--   This is based on Caminada's algorithm for computing semi-stable labellings,
--   with all checks removed.
completions :: Ord arg => Model arg -> [Context arg]
completions model@(Abst args atcks) = 
    let cgts = cogentify args
        candidates :: Eq arg => Model arg -> Context arg -> [Context arg]
        candidates model cxt =
            case filter (contradictive model cxt) cxt of
                []           -> case filter (incogentifiable model cxt) cxt of
                                    []   -> [cxt]
                                    labs -> concatMap (candidates model) $ map (transit model cxt . fst) labs
                ((a, _) : _) -> candidates model (transit model cxt a)
    in  nub . map sort $ candidates model cgts

transit :: Eq arg => Model arg -> Context arg -> arg -> Context arg
transit model cxt a =
    let cxt' = (a, Incogent) : delete (a, Cogent) cxt
        bs    = a : tails model a
        (uctns, rem) =
            partition (\ lab@(b, l) -> b `elem` bs && cogentifiable model cxt' lab) cxt'
    in  map (\ (a, _) -> (a, Uncertain)) uctns ++ rem

-- * "Preferablities"
-- | Computes all preferred labellings for the abstract model, by taking the 
--   maximally in complete labellings.
preferabilities :: Ord arg => Model arg -> [Context arg]
preferabilities model@(Abst args atcks) = 
    let cmpls = completions model
    in  filter (preferred model cmpls) cmpls

-- * "Stabilities"
-- | Computes all stable labellings for the abstract model, by keeping only
--   those labellings with no 'Uncertain' labels.
stabilities :: Ord arg => Model arg -> [Context arg]
stabilities model@(Abst args atcks) = 
    let cmpls = completions model
    in  filter (stable model cmpls) cmpls

-- * "Semi-stabilities"
-- | Computes all semi-stable labellings for the abstract model, by taking
--   the minimally undecided complete labellings.
semistabilities :: Ord arg => Model arg -> [Context arg]
semistabilities model@(Abst args atcks) = 
    let cmpls = completions model
    in  filter (semistable model cmpls) cmpls

-- * "Expand"
-- | Computes all extensions for the abstract model, with respect to the
--   given labelling.
expand :: Ord arg => Model arg -> (Model arg -> [Context arg]) -> [[arg]]
expand model ext =
    [[arg | (arg, Cogent) <- cxt] | cxt <- ext model]
