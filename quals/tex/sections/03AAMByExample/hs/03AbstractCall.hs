call :: delta -> aam -> Time aam -> Env aam -> Store delta aam -> Call -> Set (Call, Env aam, Store delta aam)
call delta aam t e s (If a tc fc) =
  eachInSet (atom delta e s a) $ \ b -> 
    setSingleton $ (if b then tc else fc, e, s)
call delta aam t e s (App fa xas) =
  eachInSet (atom delta e s fa) $ \ v ->
    eachInSet (elimClo delta v) $ \ xs c e' ->
      setFromMaybe $ bindMany aam t xs xas e' s
call _ _ _ e s (Halt a) = setSingleton (Halt a, e, s)
