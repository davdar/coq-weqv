module Lang.AAM where

import Datatypes
import Classes
import Lang.CPS

class AAM aam where
  type Addr (aam :: *) :: *
  type Time (aam :: *) :: *
  tzero :: aam -> Time aam
  tick :: aam -> Call -> Time aam -> Time aam
  alloc :: aam -> Name -> Time aam -> Addr aam

class Delta delta where
  type Val (delta :: *) :: *
  lit :: delta -> Lit -> Val delta aam
  clo :: delta -> [Name] -> Call -> Env aam -> Val delta aam
  op :: delta -> Op -> Val delta aam -> Maybe (Val delta aam)
  elimBool :: delta -> Val delta aam -> Set Bool
  elimClo :: delta -> Val delta aam -> Set ([Name], Call, Env aam)

type Env aam = Map Name (Addr aam)
type Store delta aam = Map (Addr aam) (Set (Val delta aam))

atom :: delta -> Env aam -> Store delta aam -> Atom -> Set (Val delta aam)
atom delta _ _ (LitA l) = setSingleton $ lit delta l
atom _     e s (Var x) = case mapLookup x e of
  Nothing -> Nothing
  Just l -> mapLookup l s
atom delta e s (Prim o a) = case atom delta e s a of
  Nothing -> Nothing
  Just vS -> setPartialMap (op delta o) vS
atom delta e _ (Lam xs c) = setSingleton $ clo delta xs c e

bindMany :: aam -> Time aam -> [Name] -> [Atom] -> Env aam -> Store delta aam -> Maybe (Env aam, Store delta aam)
bindMany _   _ [] [] e s = Just (e, s)
bindMany aam t (x:xs) (xa:xas) e s = case bindMany aam xs xas e of
  Nothing -> Nothing
  Just (e', s') ->
    let l = alloc aam x t
    in Just (mapInsert x l e', mapInsertWith (\/) l xv s')
bindMany _ _ _ _ _ _ = Nothing

call :: delta -> aam -> Time aam -> Env aam -> Store delta aam -> Call -> Set (Call, Env aam, Store delta aam)
call delta aam t e s (If a tc fc) =
  eachInSet (atom delta e s a) $ \ b -> 
    setSingleton $ (if b then tc else fc, e, s)
call delta aam t e s (App fa xas) =
  eachInSet (atom delta e s fa) $ \ v ->
    eachInSet (elimClo delta v) $ \ xs c e' ->
      setFromMaybe $ bindMany aam t xs xas e' s
call _ _ _ e s (Halt a) = setSingleton (Halt a, e, s)

step :: delta -> aam -> Set (Call, Env aam, Store delta aam, Time aam) -> Set (Call, Env aam, Store delta aam, Time aam)
step delta aam ss = eachInSet ss $ \ (c,e,s,t) -> 
  eachInSet (call delta aam t c e s) $ \ (c',e',s') ->
    setSingleton (c',e',s',tick aam c' t)

exec :: delta -> aam -> Call -> Set (Call, Env aam, Store delta aam, Time aam)
exec delta aam c0 = iter (collect (step delta aam)) $ setSingleton (c0, mapEmpty, mapEmpty, tzero aam)
