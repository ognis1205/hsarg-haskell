import DSL.Abstract.Api

type Literal =  String 
a, b, c  :: Literal
a        =  "A"
b        =  "B"
c        =  "C"
example1 :: Model Literal
example1 =  Abst [a, b, c] [(a, b), (b, c)]
example2 :: Model Literal
example2 =  Abst [a, b] [(a, b), (b, a)]
d, e     :: Literal
d        =  "D"
e        =  "E"
example3 :: Model Literal
example3 =  Abst [a, b, c, d] [(a, a), (a, c), (b, c), (c, d)]
example4 :: Model Literal
example4 =  Abst [a, b, c, d, e] [(a, b), (b, a), (b, c), (c, d), (d, e), (e, c)]
