module Datatypes.Point where

import Classes

data Point a = Bot | Top | Point a

instance (PartialOrder a) => PartialOrder (Point a) where
  Bot       >?< Bot       = Just EQ
  Bot       >?< _         = Just LT
  _         >?< Bot       = Just GT
  Top       >?< Top       = Just EQ
  Top       >?< _         = Just GT
  _         >?< Top       = Just LT
  (Point x) >?< (Point y) = x >?< y
instance Pointed Point where
  point = Point
instance Monad Point where
  return = point
  Bot >>= _ = Bot
  Top >>= _ = Top
  Point x >>= f = f x
instance MonadPlus Point where
  mzero = Bot
  Bot <+> x = x
  x <+> Bot = x
  Top <+> _ = Top
  _ <+> Top = Top
  Point _ <+> Point _ = Top

newtype PointT m a = PointT { runPointT :: m (Point a) }

instance Pointed m => Pointed (PointT m) where
  point = PointT . point . Point
instance Monad m => Monad (PointT m) where
  return = PointT . return . Point
  aMM >>= f = PointT $ do
    runPointT aMM >>= \case
      Bot -> return Bot
      Top -> return Top
      Point x -> runPointT $ f x
instance PartialOrderF Point where
  partialOrderF = PartialOrderW
