class AAM aam where
  type Addr (aam :: *) :: *
  type Time (aam :: *) :: *
  tzero :: aam -> Time aam
  tick :: aam -> Time aam -> Time aam
  alloc :: aam -> Name -> Time aam -> Addr aam

type Env aam = Map Name (Addr aam)
type Store aam = Map (Addr aam) (Val aam)
data Val aam = LitV Lit | Clo [Name] Call (Env aam)
type StateSpace aam = Maybe (Call, Env aam, Store aam, Time aam)
