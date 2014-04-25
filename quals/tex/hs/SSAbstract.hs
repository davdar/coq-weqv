type Env = Map Name (Set Val)
data Val = IntV | BoolV | Clo [Name] Call
type SS = (Set Call, Env)
