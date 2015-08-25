import DSL.Translated.Api
import DSL.Abstract.Api
import DSL.Structured.Api
import qualified DSL.Structured.Api as Structured

argument1, argument2, argument3 :: Argument
argument1 = argument ["kill", "intent"] []              "murder"
argument2 = argument ["witness"]        ["unreliable"]  "intent"
argument3 = argument ["witness2"]       ["unreliable2"] "-intent"

threads1 :: Threads
threads1 =  threads [argument1, argument2, argument3]

importance :: Importance
importance arg | arg == argument1  = 0.8
importance arg | arg == argument2  = 0.3
importance arg | arg == argument3  = 0.8
importance _                       = error "no importance assigned"

assumptions :: [Proposition]
assumptions = map proposition ["kill", "witness", "witness2", "unreliable2"]

audience :: Audience
audience =  (assumptions, importance)

semantics :: Semantics
semantics (_, "intent") = BeyondReasonableDoubt 
semantics _             = Scintilla
 
example :: Structured.Model
example =  Strct (threads1, audience, semantics)
