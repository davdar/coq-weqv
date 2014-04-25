bindMany :: aam -> Time aam -> [Name] -> [Atom] -> Env aam -> Store delta aam -> Maybe (Env aam, Store delta aam)
bindMany _   _ [] [] e s = Just (e, s)
bindMany aam t (x:xs) (xa:xas) e s = case bindMany aam xs xas e of
  Nothing -> Nothing
  Just (e', s') ->
    let l = alloc aam x t
    in Just (mapInsert x l e', mapInsertWith (\/) l xv s')
bindMany _ _ _ _ _ _ = Nothing
