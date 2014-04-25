module Classes.MonadPlus where

import Data.List

class (Monad m) => MonadPlus m where
  mzero :: m a
  (<+>) :: m a -> m a -> m a

msum :: (MonadPlus m) => [m a] -> m a
msum = foldl' (<+>) mzero
