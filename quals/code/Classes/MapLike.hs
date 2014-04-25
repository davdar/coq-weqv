module Classes.MapLike where

import GHC.Exts (Constraint)
import Classes.JoinLattice
import Classes.PartialOrder

class MapLike t where
  type MapKey t :: * -> Constraint
  type MapVal t :: * -> Constraint
  mapEmpty :: (MapKey t k, MapVal t v) => t k v
  mapUnion  :: (MapKey t k, MapVal t v, JoinLattice v) => t k v -> t k v -> t k v
  mapInsertWith :: (MapKey t k, MapVal t v) => (v -> v -> v) -> k -> v -> t k v -> t k v
  mapLookup :: (MapKey t k, MapVal t v) => k -> t k v -> Maybe v
  mapMap :: (MapKey t k, MapVal t v, MapVal t v') => (k -> v -> v') -> t k v -> t k v'
  mapFold :: (MapKey t k, MapVal t v) => (k -> v -> a -> a) -> a -> t k v -> a

mapSingleton :: (MapLike t, MapKey t k, MapVal t v) => k -> v -> t k v
mapSingleton k v = mapInsert k v mapEmpty

mapInsert :: (MapLike t, MapKey t k, MapVal t v) => k -> v -> t k v -> t k v
mapInsert = mapInsertWith const

mapLte :: (MapLike t, MapKey t k, MapVal t v, PartialOrder v) => t k v -> t k v -> Bool
mapLte xs ys = mapFold (\ k v -> (&&) $ f k v) True xs
  where
    f k v = case mapLookup k ys of
      Nothing -> False
      Just v' -> v <?= v'
