module Classes.JoinLattice where

import Classes.PartialOrder

infixr 7 \/

class JoinLattice a where
  bot :: a
  (\/) :: a -> a -> a

data JoinLatticeW a where
  JoinLatticeW :: (JoinLattice a) => JoinLatticeW a

class JoinLattice1 t where
  joinLattice1 :: JoinLatticeW (t a)
class JoinLatticeF t where
  joinLatticeF :: (JoinLattice a) => JoinLatticeW (t a)

instance (JoinLattice a, JoinLattice b) => JoinLattice (a, b) where
  bot = (bot, bot)
  (x1, y1) \/ (x2, y2) = (x1 \/ x2, y1 \/ y2)

instance JoinLattice [a] where
  bot = bot
  (\/) = (++)

collect :: (JoinLattice a, PartialOrder a) => (a -> a) -> a -> a
collect f i = iter ((\/) i . f) i
