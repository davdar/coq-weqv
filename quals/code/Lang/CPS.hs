module Lang.CPS where

import Classes

type Name = String
data Lit = I Integer | B Bool
  deriving (Eq, Ord)
instance PartialOrder Lit where (>?<) = discreteOrder
data Op = Add1 | Sub1 | IsNonNeg
  deriving (Eq, Ord)
instance PartialOrder Op where (>?<) = discreteOrder
data Atom =
    LitA Lit
  | Var Name
  | Prim Op Atom
  | Lam [Name] Call
  deriving (Eq, Ord)
instance PartialOrder Atom where (>?<) = discreteOrder
data Call =
    If Atom Call Call
  | App Atom [Atom]
  | Halt Atom
  deriving (Eq, Ord)
instance PartialOrder Call where (>?<) = discreteOrder

