call :: Call -> Env -> Maybe (Call, Env)
call (If a tc fc) e = case atomic a of
  Just (BoolV True) -> Just (tc, e)
  Just (BoolV False) -> Just (fb, e)
  _ -> Nothing
call (App fa xa ka) e =
  case (atomic fa e, atomic xa e, atomic ka e) of
    (Just (CloV [x, kx] c e'), Just xv, Just kv) -> 
      Just (c, Map.insert x xv (Map.insert kx kv e'))
    _ -> Nothing
call (Ret ka xa) e = case (atomic ka, atomic xa) of
  (Just (CloV [x] c e', Just xv) -> Just (c, Map.insert x xv e')
  _ -> Nothing
call (Halt a) e = Just (Halt a, e)
