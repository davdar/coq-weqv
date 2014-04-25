op :: Op -> Val -> Set Val
op Add1 IntV = Set.singleton IntV
op Sub1 IntV = Set.singleton IntV
op IsNonNeg IntV = Set.singleton BoolV
op _ _ = Set.empty

atomic :: Atom -> Env -> Set Val
atomic (Lit (I _)) _ = Set.singleton IntV
atomic (Lit (B _)) _ = Set.singleton BoolV
atomic (Var x) e = fromMaybe Set.empty $ Map.lookup x e
atomic (Prim o a) e = setConcatMap (op o) $ atomic a e
atomic (Lam xs c) _ = Set.singleton $ CloV xs c

call :: Call -> Env -> Set (Call, Env)
call (If a tc fc) e =
  flip setConcatMap (atomic a e) $ \case
    BoolV -> Set.fromList [(tc, e), (fc, e)]
    _ -> Set.empty
call (App fa xa ka) e =
  flip setConcatMap (atomic fa e) $ \case
    CloV [xx, kx] c ->
      let update = Map.insertWith Set.union xx (atomic xa e)
                 . Map.insertWith Set.union kx (atomic ka e)
      in Set.singleton (c, update e)
    _ -> Set.empty
call (Ret ka xa) e =
  flip setConcatMap (atomic ka e) $ \case
    CloV [xx] c ->
      let update = Map.insertWith Set.union xx (atomic xa e)
      in Set.singleton (c, update e)
    _ -> Set.empty
call (Halt a) e = Set.singleton (Halt a, e)

step :: Set (Call, Env) -> Set (Call, Env)
step = setConcatMap $ \ (c,e) -> call c e

widen :: Set (Call, Env) -> (Set Call, Env)
widen ss = (Set.map fst ss, joinSet $ Set.map snd ss)

unwiden :: (Set Call, Env) -> Set (Call, Env)
unwiden (cs, e) = Set.map (,e) cs

collect :: Call -> (Set Call, Env)
collect c0 = iter f ss0
  where
    ss0 = (Set.singleton c0, bot)
    f = ljoin ss0 . widen . step . unwiden
