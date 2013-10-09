Require Import FP.Data.Relation.

Class Symmetric {A} (R:relation A) := mk_Symmetric { symmetry : forall {x y}, R x y -> R y x }.
Ltac Symmetry := apply symmetry.