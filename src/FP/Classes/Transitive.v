Require Import FP.Data.Relation.

Class Transitive {A} (R:relation A) := { transitivity : forall {x} y {z}, R x y -> R y z -> R x z }.
Ltac Transitivity y := apply (transitivity y).