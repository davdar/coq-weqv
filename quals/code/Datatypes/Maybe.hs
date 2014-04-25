module Datatypes.Maybe 
  ( module Data.Maybe
  ) where

import Classes
import Data.Maybe (fromMaybe)

instance (PartialOrder a) => PartialOrder (Maybe a) where
  Nothing >?< Nothing = Just EQ
  Nothing >?< (Just _) = Just LT
  (Just _) >?< Nothing = Just GT
  (Just x) >?< (Just y) = x >?< y


