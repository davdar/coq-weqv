type Name = String
data Lit  = I Integer | B Bool
data Op   = Add1 | Sub1 | IsNonNeg
data Atom = LitA Lit 
          | Var Name
          | Prim Op Atom 
          | Lam Name Name Call 
          | Kon Name Call                                                                      
