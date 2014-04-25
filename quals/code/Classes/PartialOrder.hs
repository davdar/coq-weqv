module Classes.PartialOrder where

class PartialOrder a where
  (>?<) :: a -> a -> Maybe Ordering
  (>?<) x y = case (x <?= y, y <?= x) of
    (True, True) -> Just EQ
    (False, True) -> Just GT
    (True, False) -> Just LT
    (False, False) -> Nothing
  (<?=) :: a -> a -> Bool
  (<?=) x y = case x >?< y of
    Just LT -> True
    Just EQ -> True
    _ -> False
data PartialOrderW a where
  PartialOrderW :: (PartialOrder a) => PartialOrderW a
class PartialOrderF t where
  partialOrderF :: (PartialOrder a) => PartialOrderW (t a)

-- basic types
instance PartialOrder Integer where
  (>?<) = discreteOrder

discreteOrder :: (Eq a) => a -> a -> Maybe Ordering
discreteOrder x y = if x == y then Just EQ else Nothing

iter :: (PartialOrder a) => (a -> a) -> a -> a
iter f = loop
  where
    loop x =
      let x' = f x
      in if x' <?= x then x else loop x'
