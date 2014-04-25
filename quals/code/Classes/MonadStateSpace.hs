module Classes.MonadStateSpace where

import Classes.Pointed

class (Monad m, Pointed (SS m)) => MonadStateSpace m where
  type SS m :: * -> *
  transition :: (a -> m b) -> SS m a -> SS m b

-- jinstance MonadStateSpace Identity where
-- j  type SS Identity = Identity
-- j  transition f = f . runIdentity 
-- jinstance Pointed Identity where
-- j  point = Identity
-- j
-- jnewtype StateTSS s m a = StateTSS { runStateTSS :: SS m (a, s) }
-- jinstance (MonadStateSpace m, JoinLattice s) => MonadStateSpace (StateT s m) where
-- j  type SS (StateT s m) = StateTSS s m
-- j  transition f aS = StateTSS $ transition (\ (a, s) -> runStateT (f a) s) $ runStateTSS aS
-- jinstance (Pointed (SS m), JoinLattice s) => Pointed (StateTSS s m) where
-- j  point = StateTSS . point . (,bot)
-- jinstance (PartialOrderF (SS m), PartialOrder s, PartialOrder a) => PartialOrder (StateTSS s m a) where
-- j  pcompare x y = case partialOrderF :: PartialOrderW (SS m (a, s)) of
-- j    PartialOrderW -> pcompare (runStateTSS x) (runStateTSS y)
-- jinstance (PartialOrderF (SS m), PartialOrder s) => PartialOrderF (StateTSS s m) where
-- j  partialOrderF = PartialOrderW
-- j
-- jnewtype SetTSS m a = SetTSS { runSetTSS :: SS m [a] }
-- jinstance (MonadStateSpace m, JoinLatticeF m) => MonadStateSpace (SetT m) where
-- j  type SS (SetT m) = SetTSS m
-- j  transition f aS = SetTSS $ transition (\ al -> runSetT $ SetT (return al) >>= f) $ runSetTSS aS
-- jinstance (Pointed (SS m)) => Pointed (SetTSS m) where
-- j  point = SetTSS . point . point
-- jinstance MonadStateSpace [] where
-- j  type SS [] = []
-- j  transition = (=<<)
-- jinstance Pointed [] where
-- j  point = (:[])
-- j
-- jnewtype PointTSS m a = PointTSS { runPointTSS :: SS m (Point a) }
-- jinstance (MonadStateSpace m) => MonadStateSpace (PointT m) where
-- j  type SS (PointT m) = PointTSS m
-- j  transition f aP = PointTSS $ transition (\ al -> runPointT $ PointT (return al) >>= f) $ runPointTSS aP
-- jinstance (Pointed (SS m)) => Pointed (PointTSS m) where
-- j  point = PointTSS . point . Point
-- jinstance MonadStateSpace Point where
-- j  type SS Point = Point
-- j  transition = (=<<)

-- interesting idea for making continuation monad a MonadStateSpace...
-- foo :: (a -> (b -> r) -> r) -> ((a -> r) -> r) -> ((b -> r) -> r)
-- foo f aM bk = aM (\ a -> f a bk)
