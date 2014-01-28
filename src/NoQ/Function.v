Notation "f $ x" := (f x) (at level 89, right associativity, only parsing).
Parameter compose : forall {A B C}, (B -> C) -> (A -> B) -> A -> C.
Infix "∙" := compose (right associativity, at level 60).

Definition uncurry {A B C} (f:A -> B -> C) (xy:A*B) : C :=
  let (x,y) := xy in f x y.
