Class Symmetric {A} (R:A -> A -> Prop) :=
  { symmetry : forall {x y}, R x y -> R y x }.