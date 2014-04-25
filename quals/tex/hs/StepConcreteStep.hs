step :: SS -> SS
step Nothing = Nothing
step (Just (c,e)) = call c e
