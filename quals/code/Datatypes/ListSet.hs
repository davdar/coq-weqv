module Datatypes.ListSet where

import Classes

newtype ListSet a = ListSet { runListSet :: [a] }
instance Monad ListSet where
  return = ListSet . (:[])
  aMM >>= k = ListSet $ concatMap (runListSet . k) $ runListSet aMM
instance MonadPlus ListSet where
  mzero = ListSet []
  m1 <+> m2 = ListSet $ runListSet m1 ++ runListSet m2

newtype SetT m a = SetT { runSetT :: m (ListSet a) }
instance (MonadPlus m) => MonadPlus (SetT m) where
  mzero = SetT mzero
  m1 <+> m2 = SetT $ runSetT m1 <+> runSetT m2

instance (MonadPlus m) => Monad (SetT m) where
  return = SetT . return . return
  aMM >>= k = SetT $ do
    xs <- runSetT aMM
    msum $ runListSet $ liftM (runSetT . k) xs


