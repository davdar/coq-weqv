data Call = If Atom Call Call 
          | App Atom Atom Atom 
          | Ret Atom Atom 
          | Halt Atom           
data Val  = LitV Lit 
          | Clo [Name] Call Env
type Env  = Map Name Val                  
type SS   = Maybe (Call, Env)

