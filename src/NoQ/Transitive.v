Require Import NoQ.Relation.

Class Transitive {A} (R:relation A) :=
  { transitivity : forall {x} y {z}, R x y -> R y z -> R x z }.