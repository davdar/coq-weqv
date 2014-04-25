module Classes.Pointed where

class Pointed t where
  point :: a -> t a
