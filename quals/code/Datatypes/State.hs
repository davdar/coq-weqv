module Datatypes.State where

class MonadState s m where
  get :: m s
  put :: s -> m ()

newtype StateT s m a = StateT { unStateT :: s -> m (a, s) }

instance (Monad m) => MonadState s (StateT s m) where
  get = StateT $ \ s -> return (s, s)
  put s = StateT $ \ _ -> return ((), s)
