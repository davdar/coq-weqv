module Datatypes.Tuple where

import Classes

instance (PartialOrder a, PartialOrder b) => PartialOrder (a, b) where
  (x1,y1) >?< (x2,y2) = case (x1 >?< x2, y1 >?< y2) of
    (Just LT, Just LT) -> Just LT
    (Just LT, Just EQ) -> Just LT
    (Just EQ, Just LT) -> Just LT
    (Just EQ, Just EQ) -> Just EQ
    (Just EQ, Just GT) -> Just GT
    (Just GT, Just EQ) -> Just GT
    (Just GT, Just GT) -> Just GT
    (Just LT, Just GT) -> Nothing
    (Just GT, Just LT) -> Nothing
    (Nothing, _      ) -> Nothing
    (_      , Nothing) -> Nothing
