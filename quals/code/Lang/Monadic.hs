module Lang.Monadic where

import Classes
import Datatypes

-- Axis:
--  delta
--  address/time
--  monad
--
-- Delta:
type family Val (d :: *) (aam :: *) :: *
type Env aam = Map Name (Addr aam)
data E aam = E aam
type instance Tagged (E aam) = Env aam
type Store d aam = Map (Addr aam) (Val d aam)
data S d aam = S d aam
type instance Tagged (S d aam) = Store d aam
data T aam = T aam
type instance Tagged (T aam) = Time aam


-- Monad:
-- (the convenient interface)
type MonadCPS d aam m = 
  ( MonadPlus m
  , MonadState (E aam) m
  , MonadState (S d aam) m
  , MonadState (T aam) m
  , MonadStateSpace m
  )
data MonadCPSW d aam m where
  MonadCPSW :: (MonadCPS d aam m) => MonadCPSW d aam m
-- (the stronger interface)
class MonadCPS' m where
  monadCPSW :: d -> aam -> MonadCPSW d aam (m d aam)

-- Analysis:
type Analysis d aam m =
  ( Delta d
  , AAM aam
  , MonadCPS d aam m
  )
type Analysis' d aam m =
  ( Delta d
  , AAM aam
  , MonadCPS' m
  )

new :: (Analysis d aam m) => d -> aam -> Name -> m (Addr aam)
new aam x = do
  t <- getT $ T aam
  put (T aam) $ tnext aam t
  return $ alloc aam t x

var :: (Analysis d aam m) => d -> aam -> Name -> m (Val d aam)
var d aam x = do
  e <- getT $ E aam
  s <- getT $ S d aam
  return $ fromMaybe bot $ do
    l <- Map.lookup x e
    Map.lookup l s

bind :: (MonadCPS d aam m) => d -> aam -> Name -> Val d aam -> m ()
bind d aam x vD = do
  l <- new aam x
  modifyT (E z) $ Map.insert x l
  modifyT (S z) $ Map.insertWith ljoin l vD

atomic :: (MonadCPS d aam m) => Atom -> M z (Val z)
atomic z (LitA l) = return $ lit z l
atomic z (Var x) = var z x
atomic z (Prim o a) = op z o =<< atomic z a
atomic z (Lam xs c) = liftM (clo z xs c) (getT $ E z)

call :: (MCPS z) => z -> Call -> M z Call
call z (If a tc fc) = do
  b <- elimBool z =<< atomic z a
  return $ if b then tc else fc
call z (App fa xa ka) = do
  ([xx, kx], c, e') <- elimClo z =<< atomic z fa
  putT (E z) e'
  bind z xx =<< atomic z xa
  bind z kx =<< atomic z ka
  return c
call z (Ret ka xa) = do
  ([xx], c, e') <- elimClo z =<< atomic z ka
  putT (E z) e'
  bind z xx =<< atomic z xa
  return c
call _ (Halt a) = return (Halt a)

exec :: forall z. (MCPS z) => z -> Call -> SS (M z) Call
exec z c = 
  case partialOrderF :: PartialOrderW (SS (M z) Call) of
    PartialOrderW -> iter f ss0
  where
    ss0 = point c
    f = transition $ call z

collect :: forall z. (MCPS z) => z -> Call -> SS (M z) Call
collect z c = case partialOrderF :: PartialOrderW (SS (M z) Call) of
  PartialOrderW -> case joinLattice1 :: JoinLatticeW (SS (M z) Call) of
    JoinLatticeW -> iter f ss0
      where
        ss0 = point c
        f = ljoin ss0 . transition (call z)

----- Concrete

data C = C
data CVal = LitC Lit | CloC [Name] Call (Env C)
  deriving (Eq)
instance PartialOrder CVal where
  pcompare = discreteOrder
type instance Addr C = Integer
data CAddr = CAddr
type instance T CAddr = Integer
type instance Val C = CVal
type instance M C = StateT (Env C) (StateT (Store C) (StateT Integer Point))

instance Delta C where
  lit :: C -> Lit -> Val C
  lit C = LitC
  clo :: C -> [Name] -> Call -> Env C -> Val C
  clo C = CloC
  elimBool :: C -> Val C -> M C Bool
  elimBool C (LitC (B b)) = return b
  elimBool C _ = mzero
  elimClo :: C -> Val C -> M C ([Name], Call, Env C)
  elimClo C (CloC xs c e) = return (xs, c, e)
  elimClo C _ = mzero
  op :: C -> Op -> Val C -> M C (Val C)
  op C Add1 (LitC (I n)) = return (LitC (I (n+1)))
  op C Sub1 (LitC (I n)) = return (LitC (I (n-1)))
  op C IsNonNeg (LitC (I n)) | n >= 0 = return (LitC (B True))
                             | otherwise = return (LitC (B False))
  op C _ _ = mzero

c_MCPS :: (forall c. (MCPS c) => c -> a) -> a
c_MCPS f = f C

----- Abstract

data Abstract z = Abstract z
data AVal z = IntA | BoolA | CloA [Name] Call (Env z)
type instance Addr (Abstract z) = Addr z
type instance Val (Abstract z) = AVal z
type instance M (Abstract z) = M z

instance (MonadPlus (M z)) => Delta (Abstract z) where
  lit :: Abstract z -> Lit -> Val (Abstract z)
  lit _ (I _) = IntA
  lit _ (B _) = BoolA
  clo :: Abstract z -> [Name] -> Call -> Env (Abstract z) -> Val (Abstract z)
  clo _ = CloA
  elimBool :: Abstract z -> Val (Abstract z) -> M (Abstract z) Bool
  elimBool _ BoolA = return True `mplus` return False
  elimBool _ _ = mzero
  elimClo :: Abstract z -> Val (Abstract z) -> M (Abstract z) ([Name], Call, Env (Abstract z))
  elimClo _ (CloA xs c e) = return (xs, c, e)
  elimClo _ _ = mzero
  op :: Abstract z -> Op -> Val (Abstract z) -> M (Abstract z) (Val (Abstract z))
  op _ Add1 IntA = return IntA
  op _ Sub1 IntA = return IntA
  op _ IsNonNeg IntA = return BoolA
  op _ _ _ = mzero

----- 0CFA

data ZCFA = ZCFA
