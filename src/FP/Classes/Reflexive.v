Require Import FP.Data.Relation.

Class Reflexive {A} (R:relation A) := mk_Reflexive { reflexivity : forall {x}, R x x }.
Ltac Reflexivity := apply reflexivity.
