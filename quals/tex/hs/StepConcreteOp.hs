op :: Op -> Val -> Maybe Val
op Add1 (Int n) = Just (Int (n+1))
op Sub1 (Int n) = Just (Int (n-1))
op IsNonNeg (Int n) | n >= 0 = Just (Bool True)
                     | otherwise = Just (Bool False)
op _ _ = Nothing
