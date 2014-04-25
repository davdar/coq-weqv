module Classes.SetLike where

import GHC.Exts (Constraint)
import Data.List (foldl')
import Classes.JoinLattice

class SetLike t where
  type SetElem t :: * -> Constraint
  setEmpty :: (SetElem t e) => t e
  setUnion :: (SetElem t e) => t e
  setInsert :: (SetElem t e) => e -> t e -> t e
  setElem :: (SetElem t e) => e -> t e -> Bool
  setMap :: (SetElem t e, SetElem t e') => (e -> e') -> t e -> t e'
  setConcatMap :: (SetElem t e, SetElem t e') => (e -> t e') -> t e -> t e'
  setFold :: (SetElem t e) => (e -> a -> a) -> a -> t e -> a

setSingleton :: (SetLike t, SetElem t e) => e -> t e
setSingleton e = setInsert e setEmpty

setFromList :: (SetLike t, SetElem t e) => [e] -> t e
setFromList = foldl' (\ s e -> setInsert e s) setEmpty

setJoins :: (SetLike t, SetElem t e, JoinLattice e) => t e -> e
setJoins = setFold (\/) bot

setPartialMap :: (SetLike t, SetElem t e, SetElem t e') => (e -> Maybe e') -> t e -> t e'
setPartialMap f = setConcatMap (maybe setEmpty setSingleton . f)
