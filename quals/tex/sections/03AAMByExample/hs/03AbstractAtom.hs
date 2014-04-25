atom :: delta -> Env aam -> Store delta aam -> Atom -> Set (Val delta aam)
atom delta _ _ (LitA l) = setSingleton $ lit delta l
atom _     e s (Var x) = case mapLookup x e of
  Nothing -> Nothing
  Just l -> mapLookup l s
atom delta e s (Prim o a) = case atom delta e s a of
  Nothing -> Nothing
  Just vS -> setPartialMap (op delta o) vS
atom delta e _ (Lam xs c) = setSingleton $ clo delta xs c e
