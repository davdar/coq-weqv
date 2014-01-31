Class Reflexive {A} (R:A -> A -> Prop) :=
  { reflexivity : forall {x}, R x x }.