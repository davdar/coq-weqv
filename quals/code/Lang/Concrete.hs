module Lang.Concrete where

import Classes
import Datatypes
import Lang.CPS

type Env = Map Name Val
data Val = LitV Lit | Clo [Name] Call Env
  deriving (Eq, Ord)
instance PartialOrder Val where (>?<) = discreteOrder
type StateSpace = Maybe (Call, Env)

op :: Op -> Val -> Maybe Val
op Add1 (LitV (I n)) = Just $ LitV $ I $ n+1
op Sub1 (LitV (I n)) = Just $ LitV $ I $ n-1
op IsNonNeg (LitV (I n)) | n >= 0 = Just $ LitV $ B True
                         | otherwise = Just $ LitV $ B False
op _ _ = Nothing

atom :: Env -> Atom -> Maybe Val
atom _ (LitA l) = Just $ LitV l
atom e (Var x) = mapLookup x e
atom e (Prim o a) = case atom e a of
  Nothing -> Nothing
  Just v -> op o v
atom e (Lam xs c) = Just $ Clo xs c e

bindMany :: [Name] -> [Atom] -> Env -> Maybe Env
bindMany [] [] e = Just e
bindMany (x:xs) (xa:xas) e = case (atom xa e, bindMany xs xas e) of
  (Just xv, Just e') -> Just (mapInsert x xv e')
  _ -> Nothing
bindMany _ _ _ = Nothing

call :: Env -> Call -> Maybe (Call, Env)
call e (If a tc fc) = case atom e a of
  Just (LitV (B True)) -> Just (tc, e)
  Just (LitV (B False)) -> Just (fc, e)
  _ -> Nothing
call e (App fa xas) =
  case atom e fa of
    Just (Clo xs c e') ->
      case bindMany xs xas e' of
        Nothing -> Nothing
        Just e'' -> Just (c, e'')
    _ -> Nothing
call e (Halt a) = Just (Halt a, e)

step :: StateSpace -> StateSpace
step Nothing = Nothing
step (Just (c, e)) = call e c

exec :: Call -> StateSpace
exec c0 = iter step $ Just (c0, mapEmpty)
