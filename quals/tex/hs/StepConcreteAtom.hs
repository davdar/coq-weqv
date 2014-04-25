atom :: Atom -> Env -> Maybe Val
atom (LitA l) e = Just (LitV l)
atom (Var x) e = Map.lookup x e
atom (Prim o a) e = case atom a of
  Just v -> op o v
  Nothing -> Nothing
atom (Lam x kx c) e = Just (Clo [x, kx] c e)
atom (Kon x c) e = Just (Clo [x] c e)
