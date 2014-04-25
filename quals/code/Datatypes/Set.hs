module Datatypes.Set
  --( module Datatypes.Set
  ( module Data.Set
  ) where

import Data.Set (Set)
import Classes
import qualified Data.Set as Set

instance (Ord a) => PartialOrder (Set a) where
  xs <?= ys = Set.foldr ((&&) . f) True xs
    where
      f x =  Set.member x ys

instance (Ord a) => JoinLattice (Set a) where
  bot = Set.empty
  (\/) = Set.union
