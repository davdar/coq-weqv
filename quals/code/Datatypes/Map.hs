module Datatypes.Map
  ( module Data.Map
  ) where

import Classes
import Data.Map (Map)
import qualified Data.Map as Map
import Datatypes.Constraint

instance MapLike Map where
  type MapKey Map = Ord
  type MapVal Map = Universal
  mapEmpty = Map.empty
  mapUnion = Map.unionWith (\/)
  mapInsertWith = Map.insertWith
  mapLookup = Map.lookup
  mapMap = Map.mapWithKey
  mapFold = Map.foldWithKey
instance (Ord k, PartialOrder v) => PartialOrder (Map k v) where (<?=) = mapLte
instance (Ord k, JoinLattice v) => JoinLattice (Map k v) where
  bot = mapEmpty
  (\/) = mapUnion
