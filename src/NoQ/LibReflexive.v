Require Import NoQ.Relation.

Class LibReflexive {A} (R:relation A) :=
  { lib_reflexivity : forall {x}, R x x }.
Ltac lib_reflexivity :=
  match goal with
  | |- ?R ?x ?x => apply (lib_reflexivity (R:=R) (x:=x))
  end.
