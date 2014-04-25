module Util where

safeZip :: [a] -> [b] -> Maybe [(a,b)]
safeZip [] [] = Just []
safeZip (x:xs) (y:ys) = do
  xys <- safeZip xs ys
  return $ (x,y) : xys
safeZip _ _ = Nothing
