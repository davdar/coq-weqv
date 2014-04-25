step :: delta -> aam -> Set (Call, Env aam, Store delta aam, Time aam) -> Set (Call, Env aam, Store delta aam, Time aam)
step delta aam ss = eachInSet ss $ \ (c,e,s,t) -> 
  eachInSet (call delta aam t c e s) $ \ (c',e',s') ->
    setSingleton (c',e',s',tick aam c' t)

exec :: delta -> aam -> Call -> Set (Call, Env aam, Store delta aam, Time aam)
exec delta aam c0 = iter (collect (step delta aam)) $ setSingleton (c0, mapEmpty, mapEmpty, tzero aam)

