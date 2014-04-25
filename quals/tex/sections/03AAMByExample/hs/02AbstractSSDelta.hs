class Delta delta where
  type Val delta :: * -> *
  lit :: delta -> Lit -> Val delta aam
  clo :: delta -> [Name] -> Call -> Env aam -> Val delta aam
  op :: delta -> Op -> Val delta aam -> Maybe (Val delta aam)
  elimBool :: delta -> Val delta aam -> Set Bool
  elimClo :: delta -> Val delta aam -> Set ([Name], Call, Env aam)
type Env addr = Map Name addr
type Store addr = Map addr (Set (Val addr))
type StateSpace addr = Set (Call, Env addr, Store addr)
